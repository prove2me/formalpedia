-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_vec_can_high
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qd_vec_can_high
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:16:40.451467+00:00
-- url     : https://prove2.me/theorems/231e082e-e67e-43ab-bf5d-790f531ae435
-- title:
--   Column Families: qd vec can high
-- statement:
--   The Column Families construction uses the qd vec can high property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/HighestVectorsEqLattice.lean#L82-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/HighestVectorsEqLattice.lean#L82-L95

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestVectorsRationalSpan
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestVectorsEqLattice
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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qd_vec_can_high {M : GLMod n} (CF : ColFam M) (R : Type) [CommRing R] (j : CF.J) :
    IsHighest M R (CF.mu j) (fun i => (CF.vec j (canT (CF.mu j)) i : R)) := by sorry
