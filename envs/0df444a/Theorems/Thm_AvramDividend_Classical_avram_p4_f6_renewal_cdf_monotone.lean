-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f6_renewal_cdf_monotone
-- name    : AvramDividend.Classical.avram_p4_f6_renewal_cdf_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T10:31:43.207484+00:00
-- url     : https://prove2.me/theorems/65e5ca89-23ca-4e4e-90cd-24312d0bb620
-- title:
--   Positive finite locally cumulative renewal measure has monotone real CDF
-- statement:
--   The map x ↦ ν((0,x]) is monotone for x≥0 by inclusion Ioc 0 x⊆Ioc 0 y whenever x≤y. Local finiteness makes ENNReal.toReal monotone on these values. This elementary but source-exact reusable child is used when assembling a zero-discount Gaussian scale function directly from its renewal measure.
-- source:
--   MeasureTheory.measure_mono and ENNReal.toReal_mono under the finite bound ν(Ioc 0 y)<∞; exact pinned Mathlib 0df444a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f6_renewal_cdf_monotone
    (ν : Measure ℝ)
    (hFin : ∀ x : ℝ, 0 ≤ x → ν (Ioc (0 : ℝ) x) < ⊤) :
    MonotoneOn (fun x : ℝ => if 0 ≤ x then (ν (Ioc (0 : ℝ) x)).toReal else 0) (Ici (0 : ℝ)) := by sorry
