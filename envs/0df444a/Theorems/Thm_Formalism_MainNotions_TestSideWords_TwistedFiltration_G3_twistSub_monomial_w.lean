-- Prove2me | Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G3_twistSub_monomial_w
-- name    : Formalism.MainNotions.TestSideWords.TwistedFiltration.G3.twistSub_monomial_w
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:12:01.377559+00:00
-- url     : https://prove2.me/theorems/321d2992-f55d-491b-89dd-7ea382907153
-- title:
--   G3: twist Sub monomial w
-- statement:
--   The G3 construction uses the twist Sub monomial w property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TwistedSubstitution/TwistedMonomialFiltration/TwistSubXMemSupported.lean#L236-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TwistedSubstitution/TwistedMonomialFiltration/TwistSubXMemSupported.lean#L236-L250

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

theorem Formalism.MainNotions.TestSideWords.TwistedFiltration.G3.twistSub_monomial_w (w : Set ι) (hd : Disjoint S w) (j : Fin n) (M' : ι × Fin n →₀ ℕ)
    (hM' : M'.filter (fun v => v.1 ∉ w) = 0) :
    twistSub (R := R) LL S j (monomial M' 1) = monomial M' 1 := by sorry
