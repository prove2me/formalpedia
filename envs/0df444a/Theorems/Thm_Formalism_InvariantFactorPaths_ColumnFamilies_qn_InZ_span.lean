-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_InZ_span
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qn_InZ_span
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:58.450797+00:00
-- url     : https://prove2.me/theorems/6d927586-1b90-42fc-acea-7c8a8b0f8931
-- title:
--   Column Families: qn In Z span
-- statement:
--   The Column Families construction uses the qn In Z span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QnEvalMap.lean#L44-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QnEvalMap.lean#L44-L58

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QnFactRowDivDiag
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QnPtEmpty
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_CoeffTransposeVariables
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QnInterlacedLowerTri
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QnEvalMap
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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qn_InZ_span (n : ℕ) (ν : Fin n → ℕ) {ι : Type} (P : ι → MvPolynomial (Fin n × Fin n) ℤ)
    (h1 : ∀ i, transposeVariables ℤ n (P i) ∈ dualWeyl ℤ n n ν) (x : MvPolynomial (Fin n × Fin n) ℚ)
    (hx : x ∈ Submodule.span ℤ (Set.range fun i => map (Int.castRingHom ℚ) (P i))) : qn_InZ n ν x := by sorry
