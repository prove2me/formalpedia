-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_ev_phQ_zero
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qd_ev_phQ_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:33:02.576164+00:00
-- url     : https://prove2.me/theorems/ea0d4108-e7f1-44a5-834f-49f0a30a9ed6
-- title:
--   Column Families: qd ev ph Q zero
-- statement:
--   The Column Families construction uses the qd ev ph Q zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/FiltrationTypeIntersection.lean#L47-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/FiltrationTypeIntersection.lean#L47-L51

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qd_ev_phQ_zero {M : GLMod n} (CF : ColFam M) (j : CF.J) (nu : Fin n → ℤ) (h : ¬ DomLE nu (CF.mu j))
    (w : TIdx (CF.mu j) → ℚ) : qb_ev M ℚ nu (qd_phQ CF j w) = 0 := by sorry
