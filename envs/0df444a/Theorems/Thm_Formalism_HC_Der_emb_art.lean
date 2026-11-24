-- Prove2me | Theorems.Thm_Formalism_HC_Der_emb_art
-- name    : Formalism.HC.Der.emb_art
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T19:53:49.263849+00:00
-- url     : https://prove2.me/theorems/30a15704-71e7-4264-81ac-e12bf384032a
-- title:
--   Der: emb art
-- statement:
--   The Der construction uses the emb art property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/CycBasic.lean#L74-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/CycBasic.lean#L74-L76

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DecompTypeI
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSymOfModEq
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycBasic
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_emb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits
variable {φ : Frame} (H : HostRaw φ)

theorem Formalism.HC.Der.emb_art (u : (ZMod H.condN)ˣ) (x : H.E) :
    emb H (H.gal.symm (H.art u) x) = tauN H.condN u (emb H x) := by sorry
