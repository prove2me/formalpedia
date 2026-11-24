-- Prove2me | Theorems.Thm_Formalism_HC_Der_kc_pairing
-- name    : Formalism.HC.Der.kc_pairing
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:54.331723+00:00
-- url     : https://prove2.me/theorems/80cc4117-4fef-41e8-aea9-18bb12b09921
-- title:
--   Der: kc pairing
-- statement:
--   The Der construction uses the kc pairing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/KcPair.lean#L61-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/KcPair.lean#L61-L140

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcPair
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HC Formalism.HC.Der
open Ideal UniqueFactorizationMonoid

theorem Formalism.HC.Der.kc_pairing {S : Type*} [CommRing S] [IsDedekindDomain S] (D : Ideal S) (hD0 : D ≠ ⊥)
    (f : Ideal S ≃* Ideal S) (hfD : f D = D) (p : Ideal S → Prop)
    (hp : ∀ P ∈ normalizedFactors D, (p (f P) ↔ ¬ p P)) :
    ∃ B : Ideal S, D = B * f B ∧ (∀ P : Ideal S, P.IsPrime → P ∣ B → p P) ∧ B ⊔ f B = ⊤ ∧
      (∀ g : Ideal S ≃* Ideal S, g D = D → (∀ P ∈ normalizedFactors D, (p (g P) ↔ p P)) → g B = B) ∧
      ∀ B' : Ideal S, D = B' * f B' → (∀ P : Ideal S, P.IsPrime → P ∣ B' → p P) → B' = B := by sorry
