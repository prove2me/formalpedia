-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_far_field_hjb_of_reserve_drift_bound
-- name    : AvramDividend.Classical.vcstar_far_field_hjb_of_reserve_drift_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T15:35:09.873996+00:00
-- url     : https://prove2.me/theorems/66d16ad7-42b9-4288-93a1-1a62dc061ed6
-- title:
--   Explicit reserve bound guarantees the full HJB equality above every finite optimal barrier
-- statement:
--   For a finite optimal barrier cstar, the full HJB equation holds for any reserve x at least one unit above the barrier whenever X.c≤q(x−cstar). This replaces a previous condition involving the unknown candidate value with an explicit drift-and-reserve inequality. The scale-function barrier value is nonnegative, so its affine continuation dominates the excess reserve x−cstar. That implies the earlier far-field generator residual condition and the derivative is one. Consequently, the global HJB difficulty is confined to an explicitly bounded region.
-- source:
--   Canonical proved nonnegative barrier value, affine vcstar continuation, and finite-barrier far-field HJB theorem.

import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.vcstar_far_field_hjb_of_reserve_drift_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hcfin : cstar W < ⊤)
    (x : ℝ) (hfar : (cstar W).toReal + 1 ≤ x)
    (hdrift : X.c ≤ q * (x - (cstar W).toReal)) :
    X.GeneratorIntegrable (vcstar W) x ∧
      max (X.generator (vcstar W) x - q * vcstar W x)
        (1 - deriv (vcstar W) x) = 0 := by sorry
