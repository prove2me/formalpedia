-- Prove2me | Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_lam1S_mul_le
-- name    : Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_lam1S_mul_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:51:34.702133+00:00
-- url     : https://prove2.me/theorems/e1a499e3-4d08-507b-9595-4cc7f61380a6
-- title:
--   G1: flt lam1 S mul le
-- statement:
--   The G1 construction uses the flt lam1 S mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TwistedSubstitution/TwistedMonomialFiltration/TMemLaurentFiltration.lean#L355-L362
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TwistedSubstitution/TwistedMonomialFiltration/TMemLaurentFiltration.lean#L355-L362

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ObjPol
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_TMemLaurentFiltration
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
open Formalism Formalism.MainNotions Formalism.MainNotions.TestSideWords Formalism.MainNotions.TestSideWords.TwistedFiltration Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
open Formalism.MainNotions.G

theorem Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_lam1S_mul_le {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (F G : MvPolynomial (ι × Fin n) R) : lam1S LL S (F * G) ≤ lam1S LL S F + lam1S LL S G := by sorry
