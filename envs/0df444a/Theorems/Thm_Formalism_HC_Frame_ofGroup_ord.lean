-- Prove2me | Theorems.Thm_Formalism_HC_Frame_ofGroup_ord
-- name    : Formalism.HC.Frame.ofGroup_ord
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:37:17.064319+00:00
-- url     : https://prove2.me/theorems/801fa559-10d9-4b02-a66a-22f82ee4dfa3
-- title:
--   Frame: of Group ord
-- statement:
--   The Frame construction uses the of Group ord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/FrameCyclicGenerator.lean#L62-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/FrameCyclicGenerator.lean#L62-L62

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
variable [Fintype A']

theorem Formalism.HC.Frame.ofGroup_ord : (ofGroup e h' hs a' hk).ord = Fintype.card A' := by sorry
