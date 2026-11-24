-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_coeff_X_pderiv
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qn_coeff_X_pderiv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:03.87787+00:00
-- url     : https://prove2.me/theorems/a1f4d932-257d-419b-b598-a631ad7ceab5
-- title:
--   Column Families: qn coeff X pderiv
-- statement:
--   The Column Families construction uses the qn coeff X pderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/CoeffTransposeVariables.lean#L12-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/CoeffTransposeVariables.lean#L12-L28

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qn_coeff_X_pderiv {σ : Type*} (i : σ) (f : MvPolynomial σ ℚ) (m : σ →₀ ℕ) :
    coeff m (X i * pderiv i f) = (m i : ℚ) * coeff m f := by sorry
