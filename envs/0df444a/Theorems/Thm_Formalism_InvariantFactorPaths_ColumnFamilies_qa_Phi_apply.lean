-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_Phi_apply
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qa_Phi_apply
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:39:51.057955+00:00
-- url     : https://prove2.me/theorems/09a6349f-2e01-40f9-a4f2-8f5d89fb4879
-- title:
--   Column Families: qa Phi apply
-- statement:
--   The Column Families construction uses the qa Phi apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/ABridge.lean#L59-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/ABridge.lean#L59-L60

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaExpEqBidetExp
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_ABridge
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qa_Phi_apply (R : Type*) [CommRing R] (n : ℕ) (u : GLCoord R n) (f : MvPolynomial (Fin n × Fin n) R) :
    qa_Phi R n u f = u * algebraMap (MvPolynomial (Fin n × Fin n) R) (GLCoord R n) (rename Prod.swap f) := by sorry
