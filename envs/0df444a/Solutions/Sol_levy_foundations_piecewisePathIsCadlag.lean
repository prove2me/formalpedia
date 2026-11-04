-- Prove2me | solution 1 for levy_foundations_piecewisePathIsCadlag
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T00:27:57.252747+00:00
-- url     : https://prove2.me/submissions/5a0225eb-d427-43e2-b4ce-142540a91582

import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Probability.HasLawExists
import Mathlib.Probability.Distributions.Exponential
import Definitions.Def_levy_foundations_isCadlag
import Definitions.Def_levy_foundations_jumpCount
import Definitions.Def_levy_foundations_piecewisePath
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal Interval

theorem cad_jumpCount_lt_iff
    (T : ℕ → ℝ) (hmono : StrictMono T) (htop : Tendsto T atTop atTop)
    (n : ℕ) (t : ℝ) :
    n < LevyFoundations.jumpCount T t ↔ T n ≤ t := by
  have hne : {m | t < T m}.Nonempty := by
    obtain ⟨m, hm⟩ := (htop.eventually_gt_atTop t).exists
    exact ⟨m, hm⟩
  unfold LevyFoundations.jumpCount
  constructor
  · intro h
    by_contra hlt
    push_neg at hlt
    exact absurd (Nat.sInf_le (show n ∈ {m | t < T m} from hlt)) (not_le.mpr h)
  · intro h
    by_contra hle
    push_neg at hle
    have hm : sInf {m | t < T m} ∈ {m | t < T m} := Nat.sInf_mem hne
    have h1 : T (sInf {m | t < T m}) ≤ T n := hmono.monotone hle
    have hm' : t < T (sInf {m | t < T m}) := hm
    linarith

theorem cad_right (T : ℕ → ℝ) (hmono : StrictMono T) (htop : Tendsto T atTop atTop)
    (t s : ℝ) (hts : t ≤ s) (hs : s < T (LevyFoundations.jumpCount T t)) :
    LevyFoundations.jumpCount T s = LevyFoundations.jumpCount T t := by
  set m := LevyFoundations.jumpCount T t with hm
  apply le_antisymm
  · by_contra h
    push_neg at h
    have := (cad_jumpCount_lt_iff T hmono htop m s).1 h
    linarith
  · by_contra h
    push_neg at h
    have h2 := (cad_jumpCount_lt_iff T hmono htop _ t).1 h
    exact lt_irrefl _ ((cad_jumpCount_lt_iff T hmono htop (LevyFoundations.jumpCount T s) s).2 (by linarith))

theorem cad_left (T : ℕ → ℝ) (hmono : StrictMono T) (htop : Tendsto T atTop atTop) (t : ℝ) :
    ∃ k, ∀ᶠ s in 𝓝[<] t, LevyFoundations.jumpCount T s = k := by
  have hne : {n | t ≤ T n}.Nonempty := (htop.eventually_ge_atTop t).exists
  have hk : ∀ n, n < sInf {n | t ≤ T n} → T n < t :=
    fun n hn => not_le.1 (Nat.notMem_of_lt_sInf hn)
  have hk2 : t ≤ T (sInf {n | t ≤ T n}) := Nat.sInf_mem hne
  refine ⟨sInf {n | t ≤ T n}, ?_⟩
  have h1 : ∀ᶠ s in 𝓝[<] t, ∀ n ∈ Finset.range (sInf {n | t ≤ T n}), T n < s :=
    (Filter.eventually_all_finset _).2 fun n hn =>
      by filter_upwards [Ioo_mem_nhdsLT (hk n (Finset.mem_range.1 hn))] with s hs using hs.1
  filter_upwards [h1, self_mem_nhdsWithin] with s hs hst
  have hst' : s < t := hst
  apply le_antisymm
  · by_contra h
    push_neg at h
    have := (cad_jumpCount_lt_iff T hmono htop _ s).1 h
    linarith
  · by_contra h
    push_neg at h
    have := hs _ (Finset.mem_range.2 h)
    exact lt_irrefl _ ((cad_jumpCount_lt_iff T hmono htop (LevyFoundations.jumpCount T s) s).2 this.le)

theorem solution {x₀ b : ℝ} {T Y : ℕ → ℝ} (hmono : StrictMono T) (htop : Tendsto T atTop atTop) :
    LevyFoundations.isCadlag (LevyFoundations.piecewisePath x₀ b T Y) := by
  intro t
  constructor
  · have hm : t < T (LevyFoundations.jumpCount T t) := by
      by_contra h
      push_neg at h
      exact lt_irrefl _ ((cad_jumpCount_lt_iff T hmono htop _ t).2 h)
    have hcont : ContinuousWithinAt
        (fun s => x₀ + b * s + ∑ n ∈ Finset.range (LevyFoundations.jumpCount T t), Y n) (Set.Ici t) t :=
      (by fun_prop : Continuous
        (fun s : ℝ => x₀ + b * s + ∑ n ∈ Finset.range (LevyFoundations.jumpCount T t), Y n)).continuousWithinAt
    refine hcont.congr_of_eventuallyEq ?_ rfl
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hm)] with s hs hs2
    simp only [LevyFoundations.piecewisePath]
    rw [cad_right T hmono htop t s hs hs2]
  · obtain ⟨k, hk⟩ := cad_left T hmono htop t
    refine ⟨x₀ + b * t + ∑ n ∈ Finset.range k, Y n, ?_⟩
    have hc : Tendsto (fun s : ℝ => x₀ + b * s + ∑ n ∈ Finset.range k, Y n) (𝓝[<] t)
        (𝓝 (x₀ + b * t + ∑ n ∈ Finset.range k, Y n)) :=
      ((by fun_prop : Continuous (fun s : ℝ => x₀ + b * s + ∑ n ∈ Finset.range k, Y n)).tendsto t).mono_left
        nhdsWithin_le_nhds
    refine hc.congr' ?_
    filter_upwards [hk] with s hs
    simp only [LevyFoundations.piecewisePath]
    rw [hs]

