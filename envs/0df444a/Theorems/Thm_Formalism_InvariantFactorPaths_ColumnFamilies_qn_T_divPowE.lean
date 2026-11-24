-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_T_divPowE
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qn_T_divPowE
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:48.365102+00:00
-- url     : https://prove2.me/theorems/db5a62ff-f653-4474-b9c4-07715b02faca
-- title:
--   Column Families: qn T div Pow E
-- statement:
--   The Column Families construction uses the qn T div Pow E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QnFactRowDivDiag.lean#L68-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QnFactRowDivDiag.lean#L68-L72

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qn_T_divPowE (n : ℕ) (a b : Fin n) (hab : a ≠ b) (k : ℕ) (f : MvPolynomial (Fin n × Fin n) ℚ) :
    transposeVariables ℚ n (divPowE (glOps ℚ n (rowLetters n) Set.univ) a b k f) = rowDiv ℚ a b k (transposeVariables ℚ n f) := by sorry
