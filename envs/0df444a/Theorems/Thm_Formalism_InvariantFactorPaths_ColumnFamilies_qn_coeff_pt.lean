-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_coeff_pt
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qn_coeff_pt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:26:47.975326+00:00
-- url     : https://prove2.me/theorems/3c166e4c-4c90-487f-84c7-fc7716724065
-- title:
--   Column Families: qn coeff pt
-- statement:
--   The Column Families construction uses the qn coeff pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QnPtEmpty.lean#L133-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QnPtEmpty.lean#L133-L152

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qn_coeff_pt (n : ℕ) (ν : Fin n → ℕ) (F : MvPolynomial (Fin n × Fin n) ℚ)
    (hF : IsWeightedHomogeneous (colW n n) F ν) (e : Fin n × Fin n →₀ ℕ) (he : LowerTri e)
    (hec : ∀ t : Fin n, ∑ a : Fin n, e (a, t) = ν t) :
    coeff (qn_off e) (aeval (qn_pt n (qn_low n)) F) = coeff e F := by sorry
