-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_ph_type
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qd_ph_type
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:48:16.598064+00:00
-- url     : https://prove2.me/theorems/ffd4083a-1ebc-46e9-9f19-e37b8dcc254c
-- title:
--   Column Families: qd ph type
-- statement:
--   The Column Families construction uses the qd ph type property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/FiltrationTypeIntersection.lean#L68-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/FiltrationTypeIntersection.lean#L68-L126

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qd_ph_type (hA : LemmaA) {M : GLMod n} (CF : ColFam M) : ∀ (N : ℕ) (j : CF.J),
    (by classical exact (univ.filter fun j' => DomLE (CF.mu j') (CF.mu j)).card) ≤ N →
    ∀ w, qd_phQ CF j w ∈ typeSum M (qd_low (CF.mu j)) := by sorry
