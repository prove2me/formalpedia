-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_ev_phQ_top
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qd_ev_phQ_top
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:31:26.232941+00:00
-- url     : https://prove2.me/theorems/29d9adca-426a-4390-bdd3-42cad428e6c0
-- title:
--   Column Families: qd ev ph Q top
-- statement:
--   The Column Families construction uses the qd ev ph Q top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/FiltrationTypeIntersection.lean#L53-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/FiltrationTypeIntersection.lean#L53-L58

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestVectorsEqLattice
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_FiltrationTypeIntersection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}
variable [NeZero n]

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qd_ev_phQ_top {M : GLMod n} (CF : ColFam M) (j : CF.J) (w : TIdx (CF.mu j) → ℚ)
    (hw : qd_Lam (CF.mu j) w = 0) : qb_ev M ℚ (CF.mu j) (qd_phQ CF j w) = 0 := by sorry
