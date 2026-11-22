-- Prove2me | Theorems.Thm_Formalism_MainNotions_Gaps_T0_total_named_real
-- name    : Formalism.MainNotions.Gaps.T0.total_named_real
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:03:04.855282+00:00
-- url     : https://prove2.me/theorems/4690c71c-4efd-4ba2-ae63-e7d44ccda71f
-- title:
--   T0: total named real
-- statement:
--   The T0 construction uses the total named real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/QuotientParamNonneg.lean#L50-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/QuotientParamNonneg.lean#L50-L98

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

theorem Formalism.MainNotions.Gaps.T0.total_named_real (d D T c G PH Pη Pd PD PQ DivisibilityWeightConstant RR γ L κ fr lδ ρ ρ' : ℝ)
    (hd : 0 ≤ d) (hD : 1 ≤ D) (hT : 1 ≤ T) (hG : 0 ≤ G) (hPH : 0 ≤ PH) (hPD : 0 ≤ PD) (hPQ : 0 ≤ PQ)
    (hκ : 0 ≤ κ) (hS2 : T * L ≤ 2 * κ) (hlδ0 : 0 ≤ lδ) (hlδ : lδ ≤ Pd)
    (hρ : ρ ≤ ρ' + 22 * D ^ 2 * d / T) (hρ' : ρ' ≤ d * (DivisibilityWeightConstant * (RR ^ 2 * c + 1 / T) / γ)) :
    d * ((D + 4) * (D + 1) * (3 * G + 9 * PH) * L + 5 * G * fr * T + lδ + 1 / 2 * T * c * Pη)
        + ρ * PD * κ + ρ' * PQ * κ ≤
      d * ((60 * G + 180 * PH + 40 * PD) * D ^ 2 * κ / T + (5 * G * fr + Pd) * T + Pη / 2 * T * c
        + DivisibilityWeightConstant * (PD + PQ) * (1 / T + RR ^ 2 * c) * κ / γ) := by sorry
