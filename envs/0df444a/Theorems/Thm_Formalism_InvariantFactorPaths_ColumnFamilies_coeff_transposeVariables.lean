-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_coeff_transposeVariables
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.coeff_transposeVariables
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:18:49.469807+00:00
-- url     : https://prove2.me/theorems/aac9eaa8-ce51-49a3-b33a-e1e2340fd642
-- title:
--   Column Families: coeff transpose Variables
-- statement:
--   The Column Families construction uses the coeff transpose Variables property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/CoeffTransposeVariables.lean#L91-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/CoeffTransposeVariables.lean#L91-L93

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.coeff_transposeVariables (n : ℕ) (g : MvPolynomial (Fin n × Fin n) ℚ) (m : Fin n × Fin n →₀ ℕ) :
    coeff (Finsupp.mapDomain Prod.swap m) (transposeVariables ℚ n g) = coeff m g := by sorry
