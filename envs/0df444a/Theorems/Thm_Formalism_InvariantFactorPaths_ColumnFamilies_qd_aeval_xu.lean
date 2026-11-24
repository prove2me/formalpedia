-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_aeval_xu
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qd_aeval_xu
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:23:09.183795+00:00
-- url     : https://prove2.me/theorems/b8e9f373-3064-40b3-aeab-a6b146e2843c
-- title:
--   Column Families: qd aeval xu
-- statement:
--   The Column Families construction uses the qd aeval xu property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/EqSmulCanonicalOfUnipotentInvariant.lean#L191-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/EqSmulCanonicalOfUnipotentInvariant.lean#L191-L201

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
omit [NeZero n]

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qd_aeval_xu (a b : Fin n) (hab : a ≠ b) (P : MvPolynomial (Fin n × Fin n) ℚ) :
    aeval (fun v : Fin n × Fin n => (qd_genPt n * qd_trans a b hab Polynomial.X).val v.2 v.1) P
      = Polynomial.map (qd_sig n).toRingHom (rowGen ℚ a b P) := by sorry
