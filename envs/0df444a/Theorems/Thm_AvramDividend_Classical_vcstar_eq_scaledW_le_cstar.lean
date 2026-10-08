-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_eq_scaledW_le_cstar
-- name    : AvramDividend.Classical.vcstar_eq_scaledW_le_cstar
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T09:15:25.753988+00:00
-- url     : https://prove2.me/theorems/3371748a-dfe1-4097-b355-d749f95f3db4
-- title:
--   Optimal barrier candidate equals its scaled scale-function branch below c-star
-- statement:
--   For any real-valued candidate scale function W and any reserve z not exceeding the real optimal-barrier parameter c-star, the optimal-barrier candidate v_cstar(z) is exactly the scaled W branch divE(W(z),scaleDeriv W(cstar)). This pointwise definitional identity isolates the first conjunct of the weighted boundary-jet theorem. It includes the boundary and negative reserves without further positivity assumptions.
-- source:
--   Definitional equation for vcstar and the below-barrier branch of barrierValue in Definitions.Def_AvramDividend_Classical_ScaleFunction; source-specific child of vcstar_scaledW_matched_weighted_jet_at_cstar.

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.vcstar_eq_scaledW_le_cstar
    (W : ℝ → ℝ) (z : ℝ) (hz : z ≤ (cstar W).toReal) :
    vcstar W z = divE (W z) (scaleDeriv W (cstar W).toReal) := by sorry
