-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_eval_rowGen
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qd_eval_rowGen
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:20:16.013612+00:00
-- url     : https://prove2.me/theorems/37a05f21-96a6-4994-a7a8-b7b7368dc958
-- title:
--   Column Families: qd eval row Gen
-- statement:
--   The Column Families construction uses the qd eval row Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/TranslatesSpanCanonical.lean#L45-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/TranslatesSpanCanonical.lean#L45-L63

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_EqSmulCanonicalOfUnipotentInvariant
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLDetUZpow
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TranslatesSpanCanonical
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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qd_eval_rowGen (a b : Fin n) (t : ℚ) (f : MvPolynomial (Fin n × Fin n) ℚ) :
    (rowGen ℚ a b f).eval (C t) = rowAct ℚ (1 + Matrix.single b a t) f := by sorry
