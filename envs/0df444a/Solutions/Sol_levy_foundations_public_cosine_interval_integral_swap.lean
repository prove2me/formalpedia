-- Prove2me | solution 1 for levy_foundations_public_cosine_interval_integral_swap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T12:32:16.103219+00:00
-- url     : https://prove2.me/submissions/6f27e934-3340-4713-86d1-d8ad7070a485

import Mathlib.Probability.Independence.CharacteristicFunction
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- Bounded cosine deficits are Fubini integrable over a finite frequency interval. -/
theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (ε : ℝ) (hε : 0 < ε) :
    (∫ ξ in (0 : ℝ)..(2 / ε), ∫ x, (1 - Real.cos (ξ * x)) ∂μ) =
      ∫ x, (∫ ξ in (0 : ℝ)..(2 / ε), (1 - Real.cos (ξ * x))) ∂μ := by
  have h_nn : ∀ (ξ x : ℝ), 0 ≤ 1 - Real.cos (ξ * x) := fun ξ x => sub_nonneg.mpr (Real.cos_le_one _)
  haveI hfin_restrict : IsFiniteMeasure (volume.restrict (Set.uIoc (0:ℝ) (2/ε))) := by
    rw [Set.uIoc_of_le (by positivity : (0:ℝ) ≤ 2/ε)]
    infer_instance
  have hfubini_int : Integrable (fun p : ℝ × ℝ => 1 - Real.cos (p.1 * p.2))
      ((volume.restrict (Set.uIoc 0 (2/ε))).prod μ) :=
    Integrable.of_bound
      ((continuous_const.sub (Real.continuous_cos.comp
        (continuous_fst.mul continuous_snd))).aestronglyMeasurable)
      2
      (ae_of_all _ fun p => by
        simp only [Real.norm_eq_abs, abs_of_nonneg (h_nn p.1 p.2)]
        linarith [Real.neg_one_le_cos (p.1 * p.2)])
  exact intervalIntegral_integral_swap hfubini_int
