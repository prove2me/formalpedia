-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_PhiZ_apply
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qa_PhiZ_apply
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:39:47.744865+00:00
-- url     : https://prove2.me/theorems/4c61ea10-1630-438f-87ae-0d0a24e146bf
-- title:
--   Column Families: qa Phi Z apply
-- statement:
--   The Column Families construction uses the qa Phi Z apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/ABridge.lean#L76-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/ABridge.lean#L76-L77

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qa_PhiZ_apply (n : ℕ) (u : GLCoord ℤ n) (f : MvPolynomial (Fin n × Fin n) ℤ) :
    qa_PhiZ n u f = u * algebraMap (MvPolynomial (Fin n × Fin n) ℤ) (GLCoord ℤ n) (rename Prod.swap f) := by sorry
