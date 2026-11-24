-- Prove2me | Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G3_twistSub_X_mem_supported
-- name    : Formalism.MainNotions.TestSideWords.TwistedFiltration.G3.twistSub_X_mem_supported
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:12:18.313988+00:00
-- url     : https://prove2.me/theorems/a29b15b0-5082-407c-bc89-34cbd001a427
-- title:
--   G3: twist Sub X mem supported
-- statement:
--   The G3 construction uses the twist Sub X mem supported property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TwistedSubstitution/TwistedMonomialFiltration/TwistSubXMemSupported.lean#L207-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TwistedSubstitution/TwistedMonomialFiltration/TwistSubXMemSupported.lean#L207-L216

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

theorem Formalism.MainNotions.TestSideWords.TwistedFiltration.G3.twistSub_X_mem_supported (w : Set ι) (j : Fin n) (v : ι × Fin n) (hv : v.1 ∉ w) :
    twistSub (R := R) LL S j (X v) ∈ supported (GLLaurent R n) {x : ι × Fin n | x.1 ∉ w} := by sorry
