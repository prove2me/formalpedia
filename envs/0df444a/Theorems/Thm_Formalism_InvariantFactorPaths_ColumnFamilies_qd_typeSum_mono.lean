-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_typeSum_mono
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qd_typeSum_mono
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:33:36.28421+00:00
-- url     : https://prove2.me/theorems/99a4ac6e-ecde-4f8c-8f5d-d34127f54744
-- title:
--   Column Families: qd type Sum mono
-- statement:
--   The Column Families construction uses the qd type Sum mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/FiltrationTypeIntersection.lean#L11-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/FiltrationTypeIntersection.lean#L11-L14

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qd_typeSum_mono (M : GLMod n) {pi pi' : Set (Fin n → ℤ)} (h : pi ⊆ pi') : typeSum M pi ≤ typeSum M pi' := by sorry
