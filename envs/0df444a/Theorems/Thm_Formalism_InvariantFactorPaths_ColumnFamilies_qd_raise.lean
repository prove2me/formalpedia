-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_raise
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qd_raise
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:27.501843+00:00
-- url     : https://prove2.me/theorems/dc908da9-be85-4288-b9e1-8bc6ff20bc90
-- title:
--   Column Families: qd raise
-- statement:
--   The Column Families construction uses the qd raise property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/EqSmulCanonicalOfUnipotentInvariant.lean#L215-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/EqSmulCanonicalOfUnipotentInvariant.lean#L215-L224

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qd_raise (mu : Fin n → ℤ) (P : MvPolynomial (Fin n × Fin n) ℚ) (a b : Fin n) (hab : a ≠ b)
    (h : evGLR (R := ℚ) (qd_genPt n * qd_trans a b hab Polynomial.X) (qd_L mu P)
      = evGLR (R := ℚ) (qd_genPt n) (qd_L mu P)) :
    rowGen ℚ a b P = Polynomial.C P := by sorry
