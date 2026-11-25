-- Prove2me | Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G3_twistSub_wCoeff
-- name    : Formalism.MainNotions.TestSideWords.TwistedFiltration.G3.twistSub_wCoeff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:54:30.317864+00:00
-- url     : https://prove2.me/theorems/3b95b375-d656-4a9d-b8e7-dab2597c6cd2
-- title:
--   G3: twist Sub w Coeff
-- statement:
--   The G3 construction uses the twist Sub w Coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TwistedSubstitution/TwistedMonomialFiltration/TwistSubXMemSupported.lean#L252-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TwistedSubstitution/TwistedMonomialFiltration/TwistSubXMemSupported.lean#L252-L259

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

theorem Formalism.MainNotions.TestSideWords.TwistedFiltration.G3.twistSub_wCoeff (w : Set ι) (hd : Disjoint S w) (j : Fin n) (M : ι × Fin n →₀ ℕ)
    (F : MvPolynomial (ι × Fin n) R) : twistSub LL S j (wCoeff w M F) = wCoeff w M (twistSub LL S j F) := by sorry
