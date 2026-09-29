-- Prove2me | solution 1 for weighted_sum_chebyshev_lower_tail_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-07-03T22:42:50.366863+00:00
-- url     : https://prove2.me/submissions/9e0b3cc2-b580-4945-8189-782be9f4aa4f

/-
Solution for `weighted_sum_chebyshev_lower_tail_bound`.

Chebyshev lower tail for a weighted sum of i.i.d. centered unit-variance noise
over `Measure.pi`:  `P[∑ aᵢzᵢ ≥ −c] ≥ 1 − (∑aᵢ²)/c²`.

Route: `hvar` forces `z ∈ L²(noise)`; coordinates transport through
`measurePreserving_eval`; `variance_sum_pi` gives `Var(∑ aᵢzᵢ) = ∑ aᵢ²`;
`meas_ge_le_variance_div_sq` (Chebyshev) bounds the bad event `{|∑ aᵢzᵢ| ≥ c}`.
-/
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Moments.Variance

open MeasureTheory ProbabilityTheory Real Set

theorem solution
    (N : ℕ) (noise : Measure ℝ) [IsProbabilityMeasure noise]
    (a : Fin N → ℝ) (c : ℝ)
    (hmean : ∫ z, z ∂noise = 0) (hvar : ∫ z, z ^ 2 ∂noise = 1)
    (hc : 0 < c) :
    1 - (∑ i, a i ^ 2) / c ^ 2 ≤
      (Measure.pi fun _ : Fin N => noise).real {z | -c ≤ ∑ i, a i * z i} := by
  set P := Measure.pi fun _ : Fin N => noise with hPdef
  -- `z ∈ L²(noise)`, forced by `hvar`
  have hz2 : Integrable (fun z : ℝ => z ^ 2) noise := by
    by_contra h
    rw [integral_undef h] at hvar
    exact absurd hvar (by norm_num)
  have hL2 : MemLp (fun z : ℝ => z) 2 noise :=
    (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).2 hz2
  have hXL2 : ∀ i : Fin N, MemLp (fun z : ℝ => a i * z) 2 noise :=
    fun i => hL2.const_mul (a i)
  have hev : ∀ i : Fin N, MeasurePreserving (Function.eval i)
      (Measure.pi fun _ : Fin N => noise) noise :=
    fun i => measurePreserving_eval _ i
  have hXP : ∀ i : Fin N, MemLp (fun ω : Fin N → ℝ => a i * ω i) 2 P :=
    fun i => (hXL2 i).comp_measurePreserving (hev i)
  have hSL2 : MemLp (fun ω : Fin N → ℝ => ∑ i, a i * ω i) 2 P :=
    memLp_finset_sum Finset.univ fun i _ => hXP i
  -- expectation of each coordinate summand, hence of the sum, is `0`
  have hEi : ∀ i : Fin N, ∫ ω : Fin N → ℝ, a i * ω i ∂P = 0 := by
    intro i
    have hcoord : ∫ ω : Fin N → ℝ, ω i ∂P = ∫ z, z ∂noise := by
      rw [← (hev i).map_eq]
      exact (integral_map (hev i).measurable.aemeasurable
        aestronglyMeasurable_id).symm
    rw [integral_const_mul, hcoord, hmean, mul_zero]
  have hES : ∫ ω : Fin N → ℝ, (∑ i, a i * ω i) ∂P = 0 := by
    rw [integral_finset_sum Finset.univ fun i _ => (hXP i).integrable one_le_two]
    exact Finset.sum_eq_zero fun i _ => hEi i
  -- variance of the sum is `∑ aᵢ²`
  have hVarnoise : Var[fun z : ℝ => z; noise] = 1 := by
    rw [variance_eq_sub hL2]
    have h2 : (fun z : ℝ => z) ^ 2 = fun z : ℝ => z ^ 2 := by
      ext z
      simp [pow_two]
    rw [h2]
    rw [hvar, hmean]
    norm_num
  have hVar : Var[fun ω : Fin N → ℝ => ∑ i, a i * ω i; P] = ∑ i, a i ^ 2 := by
    have hfun : (fun ω : Fin N → ℝ => ∑ i, a i * ω i)
        = ∑ i, fun ω : Fin N → ℝ => a i * ω i := by
      ext ω
      simp [Finset.sum_apply]
    rw [hfun, variance_sum_pi fun i => hXL2 i]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [variance_const_mul, hVarnoise, mul_one]
  -- Chebyshev on the two-sided deviation
  have hcheb := meas_ge_le_variance_div_sq (μ := P) hSL2 hc
  rw [hVar] at hcheb
  have hchebR : P.real {ω | c ≤ |(∑ i, a i * ω i) - ∫ ω : Fin N → ℝ, (∑ i, a i * ω i) ∂P|}
      ≤ (∑ i, a i ^ 2) / c ^ 2 := by
    refine le_trans (ENNReal.toReal_mono ENNReal.ofReal_ne_top hcheb) ?_
    rw [ENNReal.toReal_ofReal (div_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg (a i)) (sq_nonneg c))]
  rw [hES] at hchebR
  simp only [sub_zero] at hchebR
  -- the good event contains the complement of the Chebyshev bad event
  have hBmeas : MeasurableSet {ω : Fin N → ℝ | c ≤ |∑ i, a i * ω i|} := by
    have hSm : Measurable fun ω : Fin N → ℝ => |∑ i, a i * ω i| := by fun_prop
    exact measurableSet_le measurable_const hSm
  have hsub : {ω : Fin N → ℝ | c ≤ |∑ i, a i * ω i|}ᶜ ⊆ {z | -c ≤ ∑ i, a i * z i} := by
    intro ω hω
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hω
    have := abs_lt.1 hω
    simp only [Set.mem_setOf_eq]
    linarith [this.1]
  have hmono : P.real {ω : Fin N → ℝ | c ≤ |∑ i, a i * ω i|}ᶜ ≤
      P.real {z | -c ≤ ∑ i, a i * z i} :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
  have hcompl : P.real {ω : Fin N → ℝ | c ≤ |∑ i, a i * ω i|}ᶜ =
      1 - P.real {ω : Fin N → ℝ | c ≤ |∑ i, a i * ω i|} := by
    rw [measureReal_compl hBmeas]
    congr 1
    simp [measureReal_def]
  linarith [hmono, hcompl ▸ hmono, hchebR]
