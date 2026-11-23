-- Prove2me | Theorems.Thm_Formalism_HC_Der_kc_not_dvd_different
-- name    : Formalism.HC.Der.kc_not_dvd_different
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:12:56.649094+00:00
-- url     : https://prove2.me/theorems/7b60c15c-6c39-4415-ac98-ae3e6f12913b
-- title:
--   Der: kc not dvd different
-- statement:
--   The Der construction uses the kc not dvd different property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/KcPair.lean#L148-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/KcPair.lean#L148-L168

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
open NumberField Ideal
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

theorem Formalism.HC.Der.kc_not_dvd_different (M E : Type) [Field M] [NumberField M] [Field E] [NumberField E] [Algebra M E] [IsGalois M E]
    (P : Ideal (𝓞 E)) [P.IsPrime]
    (h : P ≠ ⊥ → ∀ σ : E ≃ₐ[M] E, (∀ x : 𝓞 E, σ • x - x ∈ P) → σ = 1) : ¬ P ∣ differentIdeal (𝓞 M) (𝓞 E) := by sorry
