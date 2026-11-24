-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_off_inj
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qn_off_inj
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:21:57.268442+00:00
-- url     : https://prove2.me/theorems/f61498c2-9bf9-40fa-94f9-7a5c8b45e4f4
-- title:
--   Column Families: qn off inj
-- statement:
--   The Column Families construction uses the qn off inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QnPtEmpty.lean#L112-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QnPtEmpty.lean#L112-L131

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qn_off_inj {n : ℕ} (ν : Fin n → ℕ) (m e : Fin n × Fin n →₀ ℕ) (hm : LowerTri m) (he : LowerTri e)
    (hmc : ∀ t : Fin n, ∑ a : Fin n, m (a, t) = ν t) (hec : ∀ t : Fin n, ∑ a : Fin n, e (a, t) = ν t)
    (h : qn_off m = qn_off e) : m = e := by sorry
