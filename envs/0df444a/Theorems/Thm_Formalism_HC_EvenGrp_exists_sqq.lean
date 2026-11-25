-- Prove2me | Theorems.Thm_Formalism_HC_EvenGrp_exists_sqq
-- name    : Formalism.HC.EvenGrp.exists_sqq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:38:20.698449+00:00
-- url     : https://prove2.me/theorems/33b7cdb4-f8ef-44b7-82bf-989ffdee81d1
-- title:
--   Even Grp: exists sqq
-- statement:
--   The Even Grp construction uses the exists sqq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/OfCharLevel.lean#L311-L314
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/OfCharLevel.lean#L311-L314

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_OfCharFrame
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ExplicitFormulaErrorOfHostConditions
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_OfCharLevel
import Theorems.Thm_Formalism_HC_CharData_exists_sqq
import Theorems.Thm_Formalism_HC_EvenData_exists_sqq

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
open Formalism.FrobeniusOrbits
open Formalism.HC.EvenGrp
variable {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M)) (e : ℕ)
variable (hev : ∀ χ ∈ Ξ, χ.Even)
variable {q d : ℕ} (hH : HostHyp q d) (hc : Nat.Coprime M (q * d)) (he : 2 ≤ e)
  (hs : ∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ M → jacobiSym (-(d : ℤ)) l = 1)

theorem Formalism.HC.EvenGrp.exists_sqq : ∃ s : (host Ξ e hev hH hc he hs).E, s ^ 2 = -((host Ξ e hev hH hc he hs).q : (host Ξ e hev hH hc he hs).E) ∧
    ∀ σ : (host Ξ e hev hH hc he hs).E ≃ₐ[ℚ] (host Ξ e hev hH hc he hs).E,
      σ s = (((((host Ξ e hev hH hc he hs).gal σ).1.1 : ℤˣ) : ℤ) : (host Ξ e hev hH hc he hs).E) * s := by sorry
