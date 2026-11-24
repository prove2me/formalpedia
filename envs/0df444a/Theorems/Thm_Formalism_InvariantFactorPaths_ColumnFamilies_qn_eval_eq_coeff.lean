-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_eval_eq_coeff
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qn_eval_eq_coeff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:18:40.186283+00:00
-- url     : https://prove2.me/theorems/8e7c0c52-91c8-47dc-a593-ee20db8ab92a
-- title:
--   Column Families: qn eval eq coeff
-- statement:
--   The Column Families construction uses the qn eval eq coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/CoeffTransposeVariables.lean#L132-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/CoeffTransposeVariables.lean#L132-L146

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TransposeVariables
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_CoeffTransposeVariables
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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qn_eval_eq_coeff (n : ℕ) (ν : Fin n → ℕ) (F : MvPolynomial (Fin n × Fin n) ℚ)
    (hF : IsWeightedHomogeneous (colW n n) F ν) :
    eval (idFrame ℚ n n) F = coeff (lhwline_mnu (le_refl n) ν) F := by sorry
