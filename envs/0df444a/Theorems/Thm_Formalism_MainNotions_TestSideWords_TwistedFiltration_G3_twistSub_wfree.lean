-- Prove2me | Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G3_twistSub_wfree
-- name    : Formalism.MainNotions.TestSideWords.TwistedFiltration.G3.twistSub_wfree
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:11:46.118799+00:00
-- url     : https://prove2.me/theorems/294c0f9e-61e7-43d5-ac82-7b58c904f39e
-- title:
--   G3: twist Sub wfree
-- statement:
--   The G3 construction uses the twist Sub wfree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TwistedSubstitution/TwistedMonomialFiltration/TwistSubXMemSupported.lean#L218-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TwistedSubstitution/TwistedMonomialFiltration/TwistSubXMemSupported.lean#L218-L234

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_MaxTwistDegreePderivLeAddOne
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_TwistSubXMemSupported
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
open Formalism Formalism.MainNotions Formalism.MainNotions.TestSideWords Formalism.MainNotions.TestSideWords.TwistedFiltration Formalism.MainNotions.TestSideWords.TwistedFiltration.G3
open Formalism.MainNotions.G Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
variable {R : Type*} [CommRing R] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
open Classical

theorem Formalism.MainNotions.TestSideWords.TwistedFiltration.G3.twistSub_wfree (w : Set ι) (j : Fin n) (P : MvPolynomial (ι × Fin n) R) (hP : WFree w P) :
    WFree w (twistSub LL S j P) := by sorry
