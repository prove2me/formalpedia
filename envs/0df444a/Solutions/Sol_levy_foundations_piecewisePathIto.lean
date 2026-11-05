-- Prove2me | solution 1 for levy_foundations_piecewisePathIto
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T11:58:35.975204+00:00
-- url     : https://prove2.me/submissions/24a39e80-c1a1-4100-99a0-312992701d5c

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

namespace Lv2Aux

section
variable {T : ℕ → ℝ}

lemma jc_spec (htop : Tendsto T atTop atTop) (t : ℝ) :
    t < T (LevyFoundations.jumpCount T t) := by
  have hne : {n | t < T n}.Nonempty := by
    obtain ⟨n, hn⟩ := (htop.eventually (eventually_gt_atTop t)).exists
    exact ⟨n, hn⟩
  exact Nat.sInf_mem hne

lemma jc_zero (t : ℝ) (h : t < T 0) : LevyFoundations.jumpCount T t = 0 :=
  Nat.eq_zero_of_le_zero (Nat.sInf_le (show 0 ∈ {n | t < T n} from h))

lemma jc_succ (hmono : StrictMono T) (htop : Tendsto T atTop atTop) (t : ℝ) (k : ℕ)
    (h1 : T k ≤ t) (h2 : t < T (k + 1)) : LevyFoundations.jumpCount T t = k + 1 := by
  apply le_antisymm
  · exact Nat.sInf_le (show k + 1 ∈ {n | t < T n} from h2)
  · by_contra hlt
    push_neg at hlt
    have h3 := jc_spec htop t
    have : T (LevyFoundations.jumpCount T t) ≤ T k := hmono.monotone (by omega)
    linarith

lemma piece (hmono : StrictMono T) (htop : Tendsto T atTop atTop)
    {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : Continuous f')
    (x₀ b : ℝ) (Y : ℕ → ℝ) (k : ℕ) (u v : ℝ) (huv : u ≤ v)
    (hlo : ∀ j, k = j + 1 → T j ≤ u) (hv : v ≤ T k) :
    IntervalIntegrable (fun s => f' (LevyFoundations.piecewisePath x₀ b T Y s) * b)
      MeasureTheory.volume u v ∧
    ∫ s in u..v, f' (LevyFoundations.piecewisePath x₀ b T Y s) * b =
      f (x₀ + b * v + ∑ n ∈ Finset.range k, Y n) - f (x₀ + b * u + ∑ n ∈ Finset.range k, Y n) := by
  set g : ℝ → ℝ := fun s => x₀ + b * s + ∑ n ∈ Finset.range k, Y n with hg
  have hgd : ∀ s, HasDerivAt g b s := by
    intro s
    have := (((hasDerivAt_id s).const_mul b).const_add x₀).add_const (∑ n ∈ Finset.range k, Y n)
    exact this.congr_deriv (mul_one b)
  have hFd : ∀ s, HasDerivAt (fun s => f (g s)) (f' (g s) * b) s := by
    intro s
    exact (hf (g s)).comp s (hgd s)
  have hgc : Continuous g := by
    rw [hg]; fun_prop
  have hψc : Continuous (fun s => f' (g s) * b) := (hf'.comp hgc).mul continuous_const
  have hψi : IntervalIntegrable (fun s => f' (g s) * b) MeasureTheory.volume u v :=
    hψc.intervalIntegrable u v
  have hjc : ∀ s, u ≤ s → s < v → LevyFoundations.jumpCount T s = k := by
    intro s hus hsv
    cases k with
    | zero => exact jc_zero s (by linarith)
    | succ j =>
      exact jc_succ hmono htop s j (le_trans (hlo j rfl) hus) (by linarith)
  have hae : ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), s ∈ Set.Ioc u v →
      f' (LevyFoundations.piecewisePath x₀ b T Y s) * b = f' (g s) * b := by
    have hne : ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), s ≠ v := by
      rw [MeasureTheory.ae_iff]; simp
    filter_upwards [hne] with s hs hmem
    have hsv : s < v := lt_of_le_of_ne hmem.2 hs
    have := hjc s hmem.1.le hsv
    simp only [LevyFoundations.piecewisePath, this, hg]
  have hae' : (fun s => f' (LevyFoundations.piecewisePath x₀ b T Y s) * b) =ᵐ[
      MeasureTheory.volume.restrict (Set.uIoc u v)] (fun s => f' (g s) * b) := by
    rw [Set.uIoc_of_le huv]
    exact (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).2 hae
  refine ⟨(intervalIntegrable_congr_ae hae').2 hψi, ?_⟩
  rw [intervalIntegral.integral_congr_ae (g := fun s => f' (g s) * b)
    (by rw [Set.uIoc_of_le huv]; exact hae)]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hFd s) hψi

lemma pT (hmono : StrictMono T) (htop : Tendsto T atTop atTop) (x₀ b : ℝ) (Y : ℕ → ℝ) (n : ℕ) :
    LevyFoundations.piecewisePath x₀ b T Y (T n) = x₀ + b * T n + ∑ i ∈ Finset.range (n + 1), Y i := by
  unfold LevyFoundations.piecewisePath
  rw [jc_succ hmono htop (T n) n le_rfl (hmono (Nat.lt_succ_self n))]

lemma step (hmono : StrictMono T) (htop : Tendsto T atTop atTop)
    {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : Continuous f')
    (x₀ b : ℝ) (Y : ℕ → ℝ) (j : ℕ)
    (hH : IntervalIntegrable (fun s => f' (LevyFoundations.piecewisePath x₀ b T Y s) * b)
        MeasureTheory.volume 0 (T j) ∧
      f (x₀ + b * T j + ∑ n ∈ Finset.range j, Y n) - f x₀ =
        (∫ s in (0:ℝ)..(T j), f' (LevyFoundations.piecewisePath x₀ b T Y s) * b) +
        ∑ n ∈ Finset.range j, (f (LevyFoundations.piecewisePath x₀ b T Y (T n)) -
          f (LevyFoundations.piecewisePath x₀ b T Y (T n) - Y n)))
    (u : ℝ) (hu1 : T j ≤ u) (hu2 : u ≤ T (j + 1)) :
    IntervalIntegrable (fun s => f' (LevyFoundations.piecewisePath x₀ b T Y s) * b)
        MeasureTheory.volume 0 u ∧
      f (x₀ + b * u + ∑ n ∈ Finset.range (j + 1), Y n) - f x₀ =
        (∫ s in (0:ℝ)..u, f' (LevyFoundations.piecewisePath x₀ b T Y s) * b) +
        ∑ n ∈ Finset.range (j + 1), (f (LevyFoundations.piecewisePath x₀ b T Y (T n)) -
          f (LevyFoundations.piecewisePath x₀ b T Y (T n) - Y n)) := by
  obtain ⟨hI, hE⟩ := hH
  obtain ⟨hI2, hE2⟩ := piece hmono htop hf hf' x₀ b Y (j + 1) (T j) u hu1
    (fun i hi => by
      have : i = j := by omega
      subst this; exact le_rfl) hu2
  refine ⟨hI.trans hI2, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hI hI2]
  have hp := pT hmono htop x₀ b Y j
  have hS : ∑ i ∈ Finset.range (j + 1), Y i = ∑ i ∈ Finset.range j, Y i + Y j :=
    Finset.sum_range_succ _ j
  have hJ : ∑ n ∈ Finset.range (j + 1), (f (LevyFoundations.piecewisePath x₀ b T Y (T n)) -
          f (LevyFoundations.piecewisePath x₀ b T Y (T n) - Y n)) =
      ∑ n ∈ Finset.range j, (f (LevyFoundations.piecewisePath x₀ b T Y (T n)) -
          f (LevyFoundations.piecewisePath x₀ b T Y (T n) - Y n)) +
      (f (LevyFoundations.piecewisePath x₀ b T Y (T j)) -
          f (LevyFoundations.piecewisePath x₀ b T Y (T j) - Y j)) := Finset.sum_range_succ _ j
  have hJj : f (LevyFoundations.piecewisePath x₀ b T Y (T j)) -
          f (LevyFoundations.piecewisePath x₀ b T Y (T j) - Y j) =
      f (x₀ + b * T j + (∑ i ∈ Finset.range j, Y i + Y j)) -
        f (x₀ + b * T j + ∑ i ∈ Finset.range j, Y i) := by
    have h3 : x₀ + b * T j + (∑ i ∈ Finset.range j, Y i + Y j) - Y j =
        x₀ + b * T j + ∑ i ∈ Finset.range j, Y i := by ring
    rw [hp, hS, h3]
  rw [hS] at hE2 ⊢
  rw [hJ, hJj]
  linarith

lemma H_all (hmono : StrictMono T) (htop : Tendsto T atTop atTop) (hpos : 0 < T 0)
    {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : Continuous f')
    (x₀ b : ℝ) (Y : ℕ → ℝ) (k : ℕ) :
    IntervalIntegrable (fun s => f' (LevyFoundations.piecewisePath x₀ b T Y s) * b)
        MeasureTheory.volume 0 (T k) ∧
      f (x₀ + b * T k + ∑ n ∈ Finset.range k, Y n) - f x₀ =
        (∫ s in (0:ℝ)..(T k), f' (LevyFoundations.piecewisePath x₀ b T Y s) * b) +
        ∑ n ∈ Finset.range k, (f (LevyFoundations.piecewisePath x₀ b T Y (T n)) -
          f (LevyFoundations.piecewisePath x₀ b T Y (T n) - Y n)) := by
  induction k with
  | zero =>
    obtain ⟨hI, hE⟩ := piece hmono htop hf hf' x₀ b Y 0 0 (T 0) hpos.le
      (fun j hj => by omega) le_rfl
    refine ⟨hI, ?_⟩
    simp only [Finset.range_zero, Finset.sum_empty, mul_zero, add_zero] at hE ⊢
    linarith
  | succ j ih =>
    exact step hmono htop hf hf' x₀ b Y j ih (T (j + 1)) (hmono.monotone (Nat.le_succ j)) le_rfl

end

end Lv2Aux

theorem solution
    {x₀ b : ℝ} {T Y : ℕ → ℝ} {f f' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : Continuous f')
    (hmono : StrictMono T) (htop : Tendsto T atTop atTop)
    (hpos : 0 < T 0) {t : ℝ} (ht : 0 ≤ t) :
    f (LevyFoundations.piecewisePath x₀ b T Y t) -
      f (LevyFoundations.piecewisePath x₀ b T Y 0) =
      (∫ s in (0:ℝ)..t, f' (LevyFoundations.piecewisePath x₀ b T Y s) * b) +
      ∑ n ∈ Finset.range (LevyFoundations.jumpCount T t),
        (f (LevyFoundations.piecewisePath x₀ b T Y (T n)) -
        f (LevyFoundations.piecewisePath x₀ b T Y (T n) - Y n)) := by
  have hp0 : LevyFoundations.jumpCount T 0 = 0 := Lv2Aux.jc_zero 0 hpos
  have hP0 : LevyFoundations.piecewisePath x₀ b T Y 0 = x₀ := by
    simp [LevyFoundations.piecewisePath, hp0]
  rw [hP0]
  by_cases h0 : t < T 0
  · have hjt : LevyFoundations.jumpCount T t = 0 := Lv2Aux.jc_zero t h0
    obtain ⟨hI, hE⟩ := Lv2Aux.piece hmono htop hf hf' x₀ b Y 0 0 t ht
      (fun j hj => by omega) h0.le
    rw [hjt]
    have hpt : LevyFoundations.piecewisePath x₀ b T Y t = x₀ + b * t := by
      simp [LevyFoundations.piecewisePath, hjt]
    rw [hpt]
    simp only [Finset.range_zero, Finset.sum_empty, mul_zero, add_zero] at hE ⊢
    linarith
  · push_neg at h0
    have hk : LevyFoundations.jumpCount T t ≠ 0 := by
      intro hk0
      have := Lv2Aux.jc_spec htop t
      rw [hk0] at this
      linarith
    obtain ⟨j, hj⟩ : ∃ j, LevyFoundations.jumpCount T t = j + 1 :=
      ⟨LevyFoundations.jumpCount T t - 1, by omega⟩
    have h1 : T j ≤ t := by
      by_contra hlt
      push_neg at hlt
      have : LevyFoundations.jumpCount T t ≤ j := Nat.sInf_le hlt
      omega
    have h2 : t < T (j + 1) := hj ▸ Lv2Aux.jc_spec htop t
    obtain ⟨hI, hE⟩ := Lv2Aux.step hmono htop hf hf' x₀ b Y j
      (Lv2Aux.H_all hmono htop hpos hf hf' x₀ b Y j) t h1 h2.le
    have hpt : LevyFoundations.piecewisePath x₀ b T Y t =
        x₀ + b * t + ∑ n ∈ Finset.range (j + 1), Y n := by
      simp only [LevyFoundations.piecewisePath, hj]
    rw [hpt, hj]
    exact hE
