-- Prove2me | Theorems.Thm_Formalism_HC_Frame_ofEquiv_h
-- name    : Formalism.HC.Frame.ofEquiv_h
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:37:11.538282+00:00
-- url     : https://prove2.me/theorems/f923eeb8-f598-4f36-99b8-267c6d360dbf
-- title:
--   Frame: of Equiv h
-- statement:
--   The Frame construction uses the of Equiv h property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/FrameCyclicGenerator.lean#L41-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/FrameCyclicGenerator.lean#L41-L42

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameCyclicGenerator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
open Formalism.HC.Frame
variable {A' : Type} [AddCommGroup A'] (e : ℕ) {n : ℕ} (ε : Idx n ≃ A') (h' : A' →+ Additive (HGrp e))
  (hs : Function.Surjective h') (a' : A') (hk : ∀ k : ℤ, h' (k • a') = 0 → k • a' = 0)

theorem Formalism.HC.Frame.ofEquiv_h (t : (ofEquiv e ε h' hs a' hk).A) :
    (ofEquiv e ε h' hs a' hk).h t = h' (ofEquivIso e ε h' hs a' hk t) := by sorry
