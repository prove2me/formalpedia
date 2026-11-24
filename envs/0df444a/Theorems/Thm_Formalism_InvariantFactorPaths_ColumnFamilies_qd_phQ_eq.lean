-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_phQ_eq
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qd_phQ_eq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:32:30.809149+00:00
-- url     : https://prove2.me/theorems/6d3bc575-0044-448a-85fb-441c26fac0e9
-- title:
--   Column Families: qd ph Q eq
-- statement:
--   The Column Families construction uses the qd ph Q eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/FiltrationTypeIntersection.lean#L23-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/FiltrationTypeIntersection.lean#L23-L26

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qd_phQ_eq {M : GLMod n} (CF : ColFam M) (j : CF.J) (w : TIdx (CF.mu j) → ℚ) :
    qd_phQ CF j w = ∑ I, w I • (fun i => (CF.vec j I i : ℚ)) := by sorry
