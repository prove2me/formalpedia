-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_can_emb
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qa_can_emb
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:39:46.995807+00:00
-- url     : https://prove2.me/theorems/5d5efa08-0eb5-4db7-bb6f-b2de8d5b6caa
-- title:
--   Column Families: qa can emb
-- statement:
--   The Column Families construction uses the qa can emb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/ABridge.lean#L11-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/ABridge.lean#L11-L16

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaExpEqBidetExp
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_ABridge
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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qa_can_emb {n : ℕ} [NeZero n] (mu : Fin n → ℤ) (c : ↥(TCols mu)) (a : Fin (colH mu c)) :
    (canT mu c).1.orderEmbOfFin (canT mu c).2 a = Fin.castLE (colH_le mu c) a := by sorry
