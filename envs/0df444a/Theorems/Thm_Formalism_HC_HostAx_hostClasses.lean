-- Prove2me | Theorems.Thm_Formalism_HC_HostAx_hostClasses
-- name    : Formalism.HC.HostAx.hostClasses
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:22:03.361439+00:00
-- url     : https://prove2.me/theorems/acd0980d-dac7-4b70-ade1-16e5dd6562ce
-- title:
--   Host Ax: host Classes
-- statement:
--   The Host Ax construction uses the host Classes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/HostFacts.lean#L279-L287
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/HostFacts.lean#L279-L287

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ConjEMemHostFIff
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_SplitK
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ExistsOpenNormalOrderOf
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Theorems.Thm_Formalism_FrobeniusOrbits_hostClasses

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

theorem Formalism.HC.HostAx.hostClasses (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ H.condN)
    (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E) (hσ : IsArithFrobAt ℤ σ P) :
    (((H.galE σ).1 = 1 ∨ (H.galE σ).1 = (-1, 1)) ↔ jacobiSym (-(H.d : ℤ)) p = 1) ∧
    ((H.galE σ).1 = (1, -1) ↔ (jacobiSym (-(H.d : ℤ)) p = -1 ∧ H.psAt p = 1)) ∧
    ((H.galE σ).1 = c0 ↔ (jacobiSym (-(H.d : ℤ)) p = -1 ∧ H.psAt p = -1)) := by sorry
