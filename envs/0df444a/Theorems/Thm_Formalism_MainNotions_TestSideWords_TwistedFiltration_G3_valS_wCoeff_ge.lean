-- Prove2me | Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G3_valS_wCoeff_ge
-- name    : Formalism.MainNotions.TestSideWords.TwistedFiltration.G3.valS_wCoeff_ge
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:12:11.265917+00:00
-- url     : https://prove2.me/theorems/c9892762-272b-4ea1-8c55-140b4f5103a5
-- title:
--   G3: val S w Coeff ge
-- statement:
--   The G3 construction uses the val S w Coeff ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TwistedSubstitution/TwistedMonomialFiltration/TwistSubXMemSupported.lean#L363-L450
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TwistedSubstitution/TwistedMonomialFiltration/TwistSubXMemSupported.lean#L363-L450

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

theorem Formalism.MainNotions.TestSideWords.TwistedFiltration.G3.valS_wCoeff_ge (w : Set ι) (hw : ∀ l ∈ w, LL.vec l = true) (hd : Disjoint S w) (F : MvPolynomial (ι × Fin n) R)
    (dw : ℕ) (hdeg : ∀ μ ∈ F.support, wDeg w μ ≤ dw) (th : ℤ) (hF : (th : WithTop ℤ) ≤ valS LL (S ∪ w) F)
    (M : ι × Fin n →₀ ℕ) : ((th - dw : ℤ) : WithTop ℤ) ≤ valS LL S (wCoeff w M F) := by sorry
