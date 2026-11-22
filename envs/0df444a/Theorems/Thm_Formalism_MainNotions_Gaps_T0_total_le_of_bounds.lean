-- Prove2me | Theorems.Thm_Formalism_MainNotions_Gaps_T0_total_le_of_bounds
-- name    : Formalism.MainNotions.Gaps.T0.total_le_of_bounds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:02:57.323281+00:00
-- url     : https://prove2.me/theorems/3d1daf4e-91a1-402d-acd9-020d479ecb32
-- title:
--   T0: total le of bounds
-- statement:
--   The T0 construction uses the total le of bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/QuotientParamNonneg.lean#L100-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/QuotientParamNonneg.lean#L100-L120

import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_FourTermSumBoundOfParameters
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_QuotientParamNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.T0

theorem Formalism.MainNotions.Gaps.T0.total_le_of_bounds (d D T c RR γ κ P1 P2 P3 P4 PP : ℝ)
    (hd : 0 ≤ d) (hT : 0 < T) (hc : 0 ≤ c) (hκ : 0 ≤ κ) (hγ : 0 < γ)
    (h1 : P1 * D ^ 2 ≤ PP ^ 2 * D ^ 3) (h2 : P2 ≤ PP ^ 3) (h3 : P3 ≤ PP ^ 2) (h4 : P4 ≤ PP ^ 2) :
    d * (P1 * D ^ 2 * κ / T + P2 * T + P3 * T * c + P4 * (1 / T + RR ^ 2 * c) * κ / γ) ≤
      d * PP ^ 2 * (D ^ 3 * κ / T + T * c + (RR ^ 2 * c + 1 / T) * κ / γ) + d * PP ^ 3 * T := by sorry
