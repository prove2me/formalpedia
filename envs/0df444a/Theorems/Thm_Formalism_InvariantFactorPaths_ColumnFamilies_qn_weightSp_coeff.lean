-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_weightSp_coeff
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qn_weightSp_coeff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:28:08.94881+00:00
-- url     : https://prove2.me/theorems/c9a19840-48ad-45e7-8bd5-96cf46ad1d52
-- title:
--   Column Families: qn weight Sp coeff
-- statement:
--   The Column Families construction uses the qn weight Sp coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/CoeffTransposeVariables.lean#L56-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/CoeffTransposeVariables.lean#L56-L66

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qn_weightSp_coeff (n : ℕ) (w : Fin n → ℤ) (z : MvPolynomial (Fin n × Fin n) ℚ)
    (hz : z ∈ weightSp (glOps ℚ n (rowLetters n) Set.univ) w) (m : Fin n × Fin n →₀ ℕ) (hm : qn_wt m ≠ w) :
    coeff m z = 0 := by sorry
