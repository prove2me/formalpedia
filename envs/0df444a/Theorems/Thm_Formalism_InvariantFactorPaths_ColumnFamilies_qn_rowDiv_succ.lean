-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_rowDiv_succ
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qn_rowDiv_succ
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:26:53.903789+00:00
-- url     : https://prove2.me/theorems/b339f735-9f1c-47d6-9e9c-bf76fa026d6e
-- title:
--   Column Families: qn row Div succ
-- statement:
--   The Column Families construction uses the qn row Div succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QnFactRowDivDiag.lean#L35-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QnFactRowDivDiag.lean#L35-L38

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TransposeVariables
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QnFactRowDivDiag
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qn_rowDiv_succ (n : ℕ) (a b : Fin n) (hab : a ≠ b) (k : ℕ) (f : MvPolynomial (Fin n × Fin n) ℚ) :
    ((k + 1 : ℕ) : ℚ) • rowDiv ℚ a b (k + 1) (transposeVariables ℚ n f) = rowDiv ℚ a b k (transposeVariables ℚ n (qn_D n a b f)) := by sorry
