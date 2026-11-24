-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_pt_step
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qn_pt_step
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:41.276175+00:00
-- url     : https://prove2.me/theorems/d96a1d2f-7fa1-4610-a624-f0f00d353cce
-- title:
--   Column Families: qn pt step
-- statement:
--   The Column Families construction uses the qn pt step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QnPtEmpty.lean#L19-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QnPtEmpty.lean#L19-L42

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qn_pt_step (n : ℕ) (D : Finset (Fin n × Fin n)) (a s : Fin n) (hw : (a, s) ∉ D)
    (hs : ∀ c, (s, c) ∉ D) (F : MvPolynomial (Fin n × Fin n) ℚ) :
    aeval (qn_pt n (insert (a, s) D)) F =
      Polynomial.eval₂ (aeval (qn_pt n D)).toRingHom (X (a, s)) (rowGen ℚ s a F) := by sorry
