-- Prove2me | Theorems.Thm_Formalism_HC_HostRaw_mem_congrGal_iff
-- name    : Formalism.HC.HostRaw.mem_congrGal_iff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T21:00:24.792228+00:00
-- url     : https://prove2.me/theorems/a77b6411-8565-49b5-abd7-16b2199f58bb
-- title:
--   Host Raw: mem congr Gal iff
-- statement:
--   The Host Raw construction uses the mem congr Gal iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimeDiscriminants/CycImage.lean#L69-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimeDiscriminants/CycImage.lean#L69-L82

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycGrp
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_CycImage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
open Formalism Formalism.HC Formalism.HC.HostRaw
open Formalism.FrobeniusOrbits Formalism.HC.Der
variable {φ : Frame} (H : HostRaw φ)

theorem Formalism.HC.HostRaw.mem_congrGal_iff {m : ℕ} (hm : m ∣ H.condN) (σ : H.E ≃ₐ[ℚ] H.E) :
    σ ∈ H.congrGal m ↔ ∃ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ 1 [MOD m] ∧ H.gal σ = H.art u := by sorry
