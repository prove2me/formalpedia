-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_brkPol_eq
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qa_brkPol_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:39:25.952351+00:00
-- url     : https://prove2.me/theorems/44ab692c-901a-4350-a687-803cb8a2122c
-- title:
--   Column Families: qa brk Pol eq
-- statement:
--   The Column Families construction uses the qa brk Pol eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/ABridge.lean#L41-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/ABridge.lean#L41-L44

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qa_brkPol_eq {n : ℕ} [NeZero n] (mu : Fin n → ℤ) (I : TIdx mu) :
    brkPol mu I = (genMat ℤ n).det ^ (mu (lastIdx n)).toNat * rename Prod.swap (qa_P ℤ I) := by sorry
