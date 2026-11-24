-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_A_can
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qd_A_can
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:32:52.76839+00:00
-- url     : https://prove2.me/theorems/9bf009f9-e30d-4476-96ba-54e095295287
-- title:
--   Column Families: qd A can
-- statement:
--   The Column Families construction uses the qd A can property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/FiltrationTypeIntersection.lean#L34-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/FiltrationTypeIntersection.lean#L34-L40

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qd_A_can {M : GLMod n} (CF : ColFam M) (j : CF.J) (g : GL (Fin n) ℚ) :
    Matrix.mulVec (M.A.map (evGL g)) (fun i => (CF.vec j (canT (CF.mu j)) i : ℚ)) =
      qd_phQ CF j (qd_gcan (CF.mu j) g) := by sorry
