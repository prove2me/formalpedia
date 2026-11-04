-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_restrict_halfline_nonatom_ext
-- name    : AvramDividend.Classical.avram_p2_c_borel_restrict_halfline_nonatom_ext
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:32:53.132064+00:00
-- url     : https://prove2.me/theorems/1306fd98-0f0e-43a2-88ad-4bbf46b40766
-- title:
--   Finite separated half-line restrictions determined by nonatom source half-line tests
-- statement:
--   Two potentially infinite real Borel measures have the same restriction to the separated negative half-line (-infinity,c] if each has finite mass there, the cutoff total masses agree, and their lower-half-line masses agree at nonatoms of the second measure below c. This yields arbitrary Borel-band equality from nonatom half-line tests while permitting infinite activity outside the cutoff.
-- source:
--   P2-C localised finite-measure Borel uniqueness based on the Proved avram_p2_c_borel_finite_measure_ext_of_nonatom_halfline_tests and pinned isFiniteMeasure_restrict. It does not assume any source Levy rate. Intended for the original Lévy separated-band expected mark measure and ν, both finite away from zero.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_c_borel_restrict_halfline_nonatom_ext
    (μ ν : Measure ℝ) (c : ℝ)
    (hμfin : μ (Iic c) ≠ ⊤) (hνfin : ν (Iic c) ≠ ⊤)
    (hcut : μ (Iic c) = ν (Iic c))
    (htests : ∀ a : ℝ, a < c → ν {a} = 0 → μ (Iic a) = ν (Iic a)) :
    μ.restrict (Iic c) = ν.restrict (Iic c) := by sorry
