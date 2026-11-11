-- Prove2me | solution 1 for levy_foundations_id_log_exp_powers_are_charFun
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-10T08:15:50.981234+00:00
-- url     : https://prove2.me/submissions/9ddce919-d324-436a-af00-dbfecfda6a10

import Mathlib
import Theorems.Thm_levy_foundations_charFun_continuous_log
import Theorems.Thm_ProbabilityTheory_leanlevy_chat16_continuous_log_unique
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_levy_foundations_isInfinitelyDivisible

open MeasureTheory ProbabilityTheory

open Filter Topology

private theorem nz_iter (ν : Measure ℝ) [IsProbabilityMeasure ν] (n : ℕ) :
    IsProbabilityMeasure (LevyFoundations.iteratedConv ν n) ∧
      ∀ ξ : ℝ, charFun (LevyFoundations.iteratedConv ν n) ξ = (charFun ν ξ) ^ n := by
  induction n with
  | zero =>
    refine ⟨by simp [LevyFoundations.iteratedConv]; infer_instance, fun ξ => ?_⟩
    simp [LevyFoundations.iteratedConv]
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨?_, fun ξ => ?_⟩
    · simp only [LevyFoundations.iteratedConv]; infer_instance
    · simp only [LevyFoundations.iteratedConv]
      rw [charFun_conv, h2, pow_succ, mul_comm]


private theorem levy_limit (μ : ℕ → ProbabilityMeasure ℝ) (f : ℝ → ℂ) (hf : ContinuousAt f 0)
    (h : ∀ t, Tendsto (fun n ↦ charFun (μ n : Measure ℝ) t) atTop (𝓝 (f t))) :
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ ∀ t, charFun ν t = f t := by
  have h_tight : IsTightMeasureSet {(μ n : Measure ℝ) | n} := by
    have := isTightMeasureSet_of_tendsto_charFun (μ := fun n => (μ n : Measure ℝ)) hf h
    simpa [Set.range] using this
  have h_compact : IsCompact (closure {μ n | n}) :=
    isCompact_closure_of_isTightMeasureSet (by simpa using h_tight)
  let U : Ultrafilter ℕ := Filter.hyperfilter ℕ
  obtain ⟨ν, -, hν⟩ := h_compact.ultrafilter_le_nhds (U.map μ)
    (.trans (by simp) (monotone_principal subset_closure))
  refine ⟨(ν : Measure ℝ), inferInstance, fun t => ?_⟩
  have h1 : Tendsto (fun n ↦ charFun (μ n : Measure ℝ) t) (U : Filter ℕ) (𝓝 (charFun (ν : Measure ℝ) t)) := by
    have hν' : Tendsto μ (U : Filter ℕ) (𝓝 ν) := hν
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ] at hν'
    simp_rw [charFun_eq_integral_innerProbChar]
    exact hν' _
  have hU : (U : Filter ℕ) ≤ atTop := by
    have := Nat.hyperfilter_le_atTop
    exact this
  exact tendsto_nhds_unique h1 ((h t).mono_left hU)



theorem solution
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : LevyFoundations.isInfinitelyDivisible μ)
    (ψ : ℝ → ℂ) (hcont : Continuous ψ) (hzero : ψ 0 = 0)
    (hchar : ∀ ξ : ℝ, charFun μ ξ = Complex.exp (ψ ξ)) :
    ∀ t : ℝ, 0 ≤ t →
      ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
        ∀ ξ : ℝ, charFun ν ξ = Complex.exp ((t : ℂ) * ψ ξ) := by
  intro t ht
  -- n-th roots have characteristic function exp (ψ / n)
  have hroot : ∀ n : ℕ, 0 < n → ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
      ∀ ξ : ℝ, charFun ν ξ = Complex.exp (ψ ξ / n) := by
    intro n hn
    obtain ⟨ν, hνp, hμν⟩ := hμ n hn
    have hpow : ∀ ξ, charFun μ ξ = (charFun ν ξ) ^ n := by
      intro ξ; rw [hμν]; exact (nz_iter ν n).2 ξ
    have hne : ∀ ξ, charFun ν ξ ≠ 0 := by
      intro ξ h
      have := hpow ξ
      rw [h, zero_pow hn.ne', hchar ξ] at this
      exact Complex.exp_ne_zero _ this
    obtain ⟨L, hLc, hL0, hL⟩ := levy_foundations_charFun_continuous_log (μ := ν) hne
    refine ⟨ν, hνp, fun ξ => ?_⟩
    have hLn : (fun ξ => (n : ℂ) * L ξ) = ψ := by
      refine ProbabilityTheory.leanlevy_chat16_continuous_log_unique
        (by fun_prop) hcont (by simp [hL0, hzero]) (fun ξ => ?_)
      rw [← hchar ξ, hpow ξ, hL ξ, ← Complex.exp_nat_mul]
    rw [hL ξ]
    congr 1
    have := congrFun hLn ξ
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
    simpa [mul_comm] using this
  -- rational times m / n
  have hrat : ∀ m n : ℕ, 0 < n → ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
      ∀ ξ : ℝ, charFun ν ξ = Complex.exp (((m : ℝ) / n : ℝ) * ψ ξ) := by
    intro m n hn
    obtain ⟨ν, hνp, hν⟩ := hroot n hn
    refine ⟨LevyFoundations.iteratedConv ν m, (nz_iter ν m).1, fun ξ => ?_⟩
    rw [(nz_iter ν m).2 ξ, hν ξ, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  -- approximate t by t_k = ⌊t (k+1)⌋ / (k+1)
  choose ν hνp hν using fun k : ℕ => hrat ⌊t * (k + 1)⌋₊ (k + 1) (Nat.succ_pos k)
  let P : ℕ → ProbabilityMeasure ℝ := fun k => ⟨ν k, hνp k⟩
  have hlim : Tendsto (fun k : ℕ => ((⌊t * (k + 1)⌋₊ : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ)) atTop (𝓝 t) := by
    have h1 : ∀ k : ℕ, t - 1 / ((k : ℝ) + 1) ≤ ((⌊t * (k + 1)⌋₊ : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ) := by
      intro k
      have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      rw [le_div_iff₀ (by push_cast; exact hk)]
      have := Nat.lt_floor_add_one (t * (k + 1))
      push_cast
      rw [sub_mul, div_mul_cancel₀ _ hk.ne']
      linarith
    have h2 : ∀ k : ℕ, ((⌊t * (k + 1)⌋₊ : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ) ≤ t := by
      intro k
      have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      rw [div_le_iff₀ (by push_cast; exact hk)]
      have := Nat.floor_le (by positivity : 0 ≤ t * (k + 1))
      push_cast
      linarith
    have hz : Tendsto (fun k : ℕ => t - 1 / ((k : ℝ) + 1)) atTop (𝓝 t) := by
      have := (tendsto_const_nhds (x := t)).sub tendsto_one_div_add_atTop_nhds_zero_nat
      simpa only [sub_zero] using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hz tendsto_const_nhds h1 h2
  have hF : ∀ ξ, Tendsto (fun k : ℕ => charFun (P k : Measure ℝ) ξ) atTop
      (𝓝 (Complex.exp ((t : ℂ) * ψ ξ))) := by
    intro ξ
    have e : ∀ k, charFun (P k : Measure ℝ) ξ
        = Complex.exp ((((⌊t * (k + 1)⌋₊ : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ) : ℝ) * ψ ξ) := fun k => hν k ξ
    simp_rw [e]
    refine ((Complex.continuous_exp.tendsto _).comp ?_)
    exact ((Complex.continuous_ofReal.tendsto t).comp hlim).mul_const (ψ ξ)
  have hfc : ContinuousAt (fun ξ : ℝ => Complex.exp ((t : ℂ) * ψ ξ)) 0 :=
    (by fun_prop : Continuous fun ξ : ℝ => Complex.exp ((t : ℂ) * ψ ξ)).continuousAt
  obtain ⟨ν', hν'p, hν'⟩ := levy_limit P _ hfc hF
  exact ⟨ν', hν'p, hν'⟩
