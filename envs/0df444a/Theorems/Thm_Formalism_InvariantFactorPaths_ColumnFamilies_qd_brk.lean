-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_brk
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qd_brk
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:23.454078+00:00
-- url     : https://prove2.me/theorems/15801d4d-6baf-41fc-adca-a0a1ddd247ef
-- title:
--   Column Families: qd brk
-- statement:
--   The Column Families construction uses the qd brk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/EqSmulCanonicalOfUnipotentInvariant.lean#L86-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/EqSmulCanonicalOfUnipotentInvariant.lean#L86-L97

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_FiltrationTheoremOfClauses
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalB
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_EqSmulCanonicalOfUnipotentInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
variable {n : ℕ}
variable [NeZero n]

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qd_brk (mu : Fin n → ℤ) (I : TIdx mu) :
    mapCoord ℚ (brk mu I) = qd_U mu * qd_sig n (qd_P mu I) := by sorry
