-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_aeval_generic_point
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.aeval_generic_point
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:48:14.34983+00:00
-- url     : https://prove2.me/theorems/841bc6c3-ed34-4f5f-8c2b-8a1f5ddd9110
-- title:
--   Column Families: aeval generic point
-- statement:
--   The Column Families construction uses the aeval generic point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/EqSmulCanonicalOfUnipotentInvariant.lean#L181-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/EqSmulCanonicalOfUnipotentInvariant.lean#L181-L188

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.aeval_generic_point (P : MvPolynomial (Fin n × Fin n) ℚ) :
    aeval (fun v : Fin n × Fin n => (qd_genPt n).val v.2 v.1) P = Polynomial.C (qd_sig n P) := by sorry
