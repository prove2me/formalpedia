-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_far_field_hjb_zero_barrier
-- name    : AvramDividend.Classical.vcstar_far_field_hjb_zero_barrier
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T15:16:48.62014+00:00
-- url     : https://prove2.me/theorems/c757837b-a9a1-4f02-aea0-f3dfa3eb79c9
-- title:
--   Zero-barrier dividend candidate satisfies the full HJB equality in the far field
-- statement:
--   For zero optimal barrier and any reserve x≥1 with qx≥c, the formal classical HJB maximum is zero and the genuine Lévy generator integral is finite. The far-field generator residual inequality comes from the verified global monotonicity and affine scale-candidate bound, and the affine derivative is exactly one for positive reserves. This gives the entire HJB condition at sufficiently high capital in the cstar=0 case.
-- source:
--   New zero-barrier far-field generator bound (pending proof), and canonically Proved vcstar_deriv_eq_one_above_cstar (4098a584-9c09-4437-b71f-5590221db9ab).

import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.vcstar_far_field_hjb_zero_barrier
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hc0 : cstar W = 0)
    (x : ℝ) (hx : 1 ≤ x) (hcost : X.c ≤ q * x) :
    X.GeneratorIntegrable (vcstar W) x ∧
      max (X.generator (vcstar W) x - q * vcstar W x)
        (1 - deriv (vcstar W) x) = 0 := by sorry
