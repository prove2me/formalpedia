-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_positive_supported_levy_sigmaFinite
-- name    : AvramDividend.Classical.gaussian_positive_supported_levy_sigmaFinite
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T18:18:48.457596+00:00
-- url     : https://prove2.me/theorems/8d1cfc16-4802-46c9-b033-af29bab9afdf
-- title:
--   Global sigma-finiteness from positive support and Lévy integrability
-- statement:
--   A measure supported on positive reals whose truncated-square positive Lévy integral is finite is sigma-finite globally, because it coincides with its positive restriction and the latter is sigma-finite.
-- source:
--   Proved gaussian_levy_positive_restrict_sigmaFinite plus Measure.restrict_eq_self_of_ae_mem and ae_iff at pinned revision.

import Mathlib
open MeasureTheory Set

theorem AvramDividend.Classical.gaussian_positive_supported_levy_sigmaFinite
    (μ : Measure ℝ)
    (hsupport : μ (Iic (0 : ℝ)) = 0)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    SigmaFinite μ := by sorry
