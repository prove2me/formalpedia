-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_mem_canT
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qb_mem_canT
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:27:31.421201+00:00
-- url     : https://prove2.me/theorems/f051cb61-369e-4225-aee3-65c19dbaafbc
-- title:
--   Column Families: qb mem can T
-- statement:
--   The Column Families construction uses the qb mem can T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/BCoreW.lean#L74-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/BCoreW.lean#L74-L79

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_FiltrationTheoremOfClauses
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreW
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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qb_mem_canT (mu : Fin n → ℤ) (c : ↥(TCols mu)) (b : Fin n) :
    b ∈ (canT mu c).1 ↔ b.val < colH mu c := by sorry
