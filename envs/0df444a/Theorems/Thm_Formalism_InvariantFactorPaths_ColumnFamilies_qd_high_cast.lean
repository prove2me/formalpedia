-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_high_cast
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qd_high_cast
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:16:46.096255+00:00
-- url     : https://prove2.me/theorems/1bfcbe20-ef1e-4c1b-8e2d-4349d35fb136
-- title:
--   Column Families: qd high cast
-- statement:
--   The Column Families construction uses the qd high cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/HighestVectorsEqLattice.lean#L97-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/HighestVectorsEqLattice.lean#L97-L105

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qd_high_cast (M : GLMod n) (mu : Fin n → ℤ) (x : M.ι → ℤ) (hx : IsHighest M ℤ mu x) :
    IsHighest M ℚ mu (fun i => (x i : ℚ)) := by sorry
