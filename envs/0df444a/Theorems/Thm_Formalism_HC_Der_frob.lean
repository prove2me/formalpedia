-- Prove2me | Theorems.Thm_Formalism_HC_Der_frob
-- name    : Formalism.HC.Der.frob
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:47:04.155413+00:00
-- url     : https://prove2.me/theorems/8c424be0-e21f-421c-bcf3-0139cbdd82c0
-- title:
--   Der: frob
-- statement:
--   The Der construction uses the frob property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/CycGrp.lean#L285-L367
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/CycGrp.lean#L285-L367

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RootEqOfSubMem
import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycGrp
import Theorems.Thm_Formalism_FrobeniusOrbits_Final_frob

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
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {φ : Frame} (H : HostRaw φ)

theorem Formalism.HC.Der.frob : ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ H.condN →
    ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})],
      (∃ σ : H.E ≃ₐ[ℚ] H.E, IsArithFrobAt ℤ σ P) ∧
      (∀ (σ : H.E ≃ₐ[ℚ] H.E) (u : (ZMod H.condN)ˣ), (u : ZMod H.condN) = (p : ZMod H.condN) →
        (IsArithFrobAt ℤ σ P ↔ H.gal σ = H.art u)) ∧
      (∀ σ : H.E ≃ₐ[ℚ] H.E, IsArithFrobAt ℤ σ P →
        (((H.gal σ).1.1 : ℤˣ) : ℤ) = H.psAt p ∧ (((H.gal σ).1.2 : ℤˣ) : ℤ) = jacobiSym (-(H.d : ℤ)) p ∧
        ∃ v : (ZMod (2 ^ (φ.e + 2)))ˣ, (v : ZMod (2 ^ (φ.e + 2))) = (p : ZMod _) ∧ φ.hH (H.gal σ).2 = hcl φ.e v) ∧
      ∀ σ : H.E ≃ₐ[ℚ] H.E, (∀ x : 𝓞 H.E, σ • x - x ∈ P) ↔ σ = 1 := by sorry
