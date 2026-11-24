-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_aeval_mul
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qd_aeval_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:56.917373+00:00
-- url     : https://prove2.me/theorems/e2b43753-e6cf-4202-a894-72aa6bc9ccb6
-- title:
--   Column Families: qd aeval mul
-- statement:
--   The Column Families construction uses the qd aeval mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/TranslatesSpanCanonical.lean#L130-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/TranslatesSpanCanonical.lean#L130-L142

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_EqSmulCanonicalOfUnipotentInvariant
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLDetUZpow
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TranslatesSpanCanonical
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qd_aeval_mul {R' : Type} [CommRing R'] [Algebra ℚ R'] (x : GL (Fin n) R') (γ : GL (Fin n) ℚ)
    (P : MvPolynomial (Fin n × Fin n) ℚ) :
    aeval (fun v : Fin n × Fin n => (x * Matrix.GeneralLinearGroup.map (algebraMap ℚ R') γ).val v.2 v.1) P
      = aeval (fun v : Fin n × Fin n => x.val v.2 v.1) (rowAct ℚ γ.val.transpose P) := by sorry
