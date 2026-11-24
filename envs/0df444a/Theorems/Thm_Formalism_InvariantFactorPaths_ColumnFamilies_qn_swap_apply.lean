-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_swap_apply
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qn_swap_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:18:18.4428+00:00
-- url     : https://prove2.me/theorems/38c8b80d-a614-419e-97cc-8113a43a493e
-- title:
--   Column Families: qn swap apply
-- statement:
--   The Column Families construction uses the qn swap apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/CoeffTransposeVariables.lean#L87-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/CoeffTransposeVariables.lean#L87-L89

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qn_swap_apply {n : ℕ} (m : Fin n × Fin n →₀ ℕ) (a l : Fin n) :
    (Finsupp.mapDomain Prod.swap m) (a, l) = m (l, a) := by sorry
