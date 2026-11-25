-- Prove2me | Theorems.Thm_Formalism_HC_HostAx_hostClassesQ
-- name    : Formalism.HC.HostAx.hostClassesQ
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:37:14.26221+00:00
-- url     : https://prove2.me/theorems/a307a9b8-f91b-53a8-84ba-ba849449a965
-- title:
--   Host Ax: host Classes Q
-- statement:
--   The Host Ax construction uses the host Classes Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/HostFacts.lean#L289-L296
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/HostFacts.lean#L289-L296

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ConjEMemHostFIff
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_SplitK
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ExistsOpenNormalOrderOf
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
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
open Formalism Formalism.HC
open Formalism.FrobeniusOrbits
open Formalism.HC.HostAx
variable {φ : Frame} (H : HostAx φ)

theorem Formalism.HC.HostAx.hostClassesQ (hP : H.PsQ) (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ H.condN)
    (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E) (hσ : IsArithFrobAt ℤ σ P) :
    (((H.galE σ).1 = 1 ∨ (H.galE σ).1 = (-1, 1)) ↔ jacobiSym (-(H.d : ℤ)) p = 1) ∧
    ((H.galE σ).1 = (1, -1) ↔ (jacobiSym (-(H.d : ℤ)) p = -1 ∧ jacobiSym (-(H.q : ℤ)) p = 1)) ∧
    ((H.galE σ).1 = c0 ↔ (jacobiSym (-(H.d : ℤ)) p = -1 ∧ jacobiSym (-(H.q : ℤ)) p = -1)) := by sorry
