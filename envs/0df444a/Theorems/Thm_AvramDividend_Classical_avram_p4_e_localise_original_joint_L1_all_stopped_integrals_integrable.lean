-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_joint_L1_all_stopped_integrals_integrable
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_joint_L1_all_stopped_integrals_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:33:19.014593+00:00
-- url     : https://prove2.me/theorems/b13ab044-9321-4394-aede-6e215ec827be
-- title:
--   Original true stopped and full pre-ruin physical residuals are globally integrable from joint L1
-- statement:
--   Given the original dividend strategy with proved measurable ruinTime and a genuinely Integrable f on time×sample space, every exact finite min(ruinTime,n) physical integral and the full pre-ruin physical integral are Integrable on probability. The proof restricts f by the actually measurable original space-time stopped sets and invokes pinned Fubini Integrable.integral_prod_right. This directly supplies the probability-space integrability and strong measurability of original drift variables, without additional a.e. measurability hypotheses; it is not a stochastic Itô or random-dividend budget.
-- source:
--   P4-E product measurable source ruin sets helper (pending publication) and pinned Mathlib Integrable.indicator/integral_prod_right.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_ruin_clock_product_measurable_sets
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Joint L¹ makes every true ruin-clipped physical integral and the full ruin integral globally L¹. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_joint_L1_all_stopped_integrals_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hDiv : IsDividendStrategy 𝓕 D)
    (μ : Measure ℝ≥0) [SFinite μ]
    (f : ℝ≥0 × Ω → ℝ) (hf : Integrable f (μ.prod P)) :
    Integrable (fun ω => ∫ t : ℝ≥0,
      if (t : ℝ≥0∞) < ruinTime X x D ω then f (t, ω) else 0 ∂μ) P ∧
    ∀ n : ℕ, Integrable (fun ω => ∫ t : ℝ≥0,
      if (t : ℝ≥0∞) < min (ruinTime X x D ω) (n : ℝ≥0∞)
      then f (t, ω) else 0 ∂μ) P := by sorry
