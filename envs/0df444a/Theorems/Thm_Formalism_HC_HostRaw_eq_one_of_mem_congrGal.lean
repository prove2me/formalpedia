-- Prove2me | Theorems.Thm_Formalism_HC_HostRaw_eq_one_of_mem_congrGal
-- name    : Formalism.HC.HostRaw.eq_one_of_mem_congrGal
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:59:16.056588+00:00
-- url     : https://prove2.me/theorems/16517ed3-3585-4c22-9d49-730d36c42487
-- title:
--   Host Raw: eq one of mem congr Gal
-- statement:
--   The Host Raw construction uses the eq one of mem congr Gal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimeDiscriminants/CycImage.lean#L141-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimeDiscriminants/CycImage.lean#L141-L157

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

theorem Formalism.HC.HostRaw.eq_one_of_mem_congrGal (hps : H.PsQ) {l : ℕ} (hl : l.Prime) (hlS : ¬ l ∣ H.QS) (σ : H.E ≃ₐ[ℚ] H.E)
    (hσ : σ ∈ H.congrGal (ordCompl[l] H.condN)) (h1 : (H.gal σ).1.1 = 1) (h2 : (H.gal σ).1.2 = 1) : σ = 1 := by sorry
