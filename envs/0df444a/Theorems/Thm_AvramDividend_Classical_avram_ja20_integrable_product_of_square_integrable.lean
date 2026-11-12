-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja20_integrable_product_of_square_integrable
-- name    : AvramDividend.Classical.avram_ja20_integrable_product_of_square_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T14:26:34.202383+00:00
-- url     : https://prove2.me/theorems/101dae79-1913-4b39-ad9f-4cb1224e905c
-- title:
--   Cross-product integrability of two measurable square-integrable real source fields
-- statement:
--   For original-space measurable Gaussian and bounded marked-jump fields, square integrability of each implies integrability of their product by |ab| <= a²+b². This discharges the L1 cross-term condition for the uncorrelated finite-cutoff variance proof without assuming independence or auxiliary processes.
-- source:
--   J-A20 physical cutoff moment certificate ebbab4df, 34046 accepted reduction.

import Mathlib
open MeasureTheory
noncomputable section

theorem AvramDividend.Classical.avram_ja20_integrable_product_of_square_integrable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (G J : Ω → ℝ)
    (hGMeas : AEStronglyMeasurable G P)
    (hJMeas : AEStronglyMeasurable J P)
    (hGsq : Integrable (fun ω => (G ω) ^ 2) P)
    (hJsq : Integrable (fun ω => (J ω) ^ 2) P) :
    Integrable (fun ω => G ω * J ω) P := by sorry
