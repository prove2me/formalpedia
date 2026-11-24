-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_prod_pt
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qn_prod_pt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:26:47.573902+00:00
-- url     : https://prove2.me/theorems/5b4a519a-180d-4270-aa32-9021fc10e54a
-- title:
--   Column Families: qn prod pt
-- statement:
--   The Column Families construction uses the qn prod pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QnPtEmpty.lean#L88-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QnPtEmpty.lean#L88-L110

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QnPtEmpty
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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qn_prod_pt (n : ℕ) (m : Fin n × Fin n →₀ ℕ) :
    (∏ i, qn_pt n (qn_low n) i ^ m i) = open Classical in if LowerTri m then monomial (qn_off m) 1 else 0 := by sorry
