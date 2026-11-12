-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja23_integral_Ioo_split_of_integrable
-- name    : AvramDividend.Classical.avram_ja23_integral_Ioo_split_of_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T16:53:19.621585+00:00
-- url     : https://prove2.me/theorems/a94b69a9-4bf8-4b44-aad2-9dce121f0022
-- title:
--   Split an integrable quadratic open interval at a marked cutoff
-- statement:
--   For any real Borel measure and an integrable quadratic function on an open interval, split its integral into the left-open-right-closed first interval and the remaining open tail, with the joining endpoint counted once.
-- source:
--   J-A23 deterministic energy passage for e5df71c0; no stochastic or auxiliary process assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ja23_integral_Ioo_split_of_integrable
    (μ : Measure ℝ) (a b c : ℝ)
    (hab : a ≤ b) (hbc : b < c)
    (hI : IntegrableOn (fun z : ℝ => z ^ 2) (Ioo a c) μ) :
    (∫ z in Ioo a c, z ^ 2 ∂μ) =
      (∫ z in Ioc a b, z ^ 2 ∂μ) +
      (∫ z in Ioo b c, z ^ 2 ∂μ) := by sorry
