-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_deriv_rowGen
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qn_deriv_rowGen
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:26:19.953996+00:00
-- url     : https://prove2.me/theorems/7aa280fe-8c07-4215-9d67-97d9673913c7
-- title:
--   Column Families: qn deriv row Gen
-- statement:
--   The Column Families construction uses the qn deriv row Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/TransposeVariables.lean#L60-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/TransposeVariables.lean#L60-L85

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementH
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TransposeVariables
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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qn_deriv_rowGen (n : ℕ) (a b : Fin n) (hab : a ≠ b) (f : MvPolynomial (Fin n × Fin n) ℚ) :
    Polynomial.derivative (rowGen ℚ a b (transposeVariables ℚ n f)) = rowGen ℚ a b (transposeVariables ℚ n (qn_D n a b f)) := by sorry
