-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_T_binomE
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qn_T_binomE
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:29.89941+00:00
-- url     : https://prove2.me/theorems/e5c6bc43-808a-4a56-b53a-92ab17d0cd8b
-- title:
--   Column Families: qn T binom E
-- statement:
--   The Column Families construction uses the qn T binom E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QnFactRowDivDiag.lean#L89-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QnFactRowDivDiag.lean#L89-L93

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qn_T_binomE (n : ℕ) (a : Fin n) (k : ℕ) (f : MvPolynomial (Fin n × Fin n) ℚ) :
    transposeVariables ℚ n (binomE (glOps ℚ n (rowLetters n) Set.univ) a k f) = rowDiv ℚ a a k (transposeVariables ℚ n f) := by sorry
