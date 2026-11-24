-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_U_inv
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qd_U_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:37.431828+00:00
-- url     : https://prove2.me/theorems/3addbbc2-7673-4aea-90e6-dee9534ceae5
-- title:
--   Column Families: qd U inv
-- statement:
--   The Column Families construction uses the qd U inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/EqSmulCanonicalOfUnipotentInvariant.lean#L209-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/EqSmulCanonicalOfUnipotentInvariant.lean#L209-L213

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qd_U_inv {R' : Type} [CommRing R'] [Algebra ℚ R'] (x u : GL (Fin n) R') (mu : Fin n → ℤ)
    (hu : Matrix.GeneralLinearGroup.det u = 1) :
    evGLR (R := ℚ) (x * u) (qd_U mu) = evGLR (R := ℚ) x (qd_U mu) := by sorry
