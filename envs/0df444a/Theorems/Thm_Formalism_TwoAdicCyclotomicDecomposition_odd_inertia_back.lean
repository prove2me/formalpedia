-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_inertia_back
-- name    : Formalism.TwoAdicCyclotomicDecomposition.odd_inertia_back
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:30:54.547057+00:00
-- url     : https://prove2.me/theorems/399b94de-39ac-4f5a-865d-94ac8d147c84
-- title:
--   Two Adic Cyclotomic Decomposition: odd inertia back
-- statement:
--   The Two Adic Cyclotomic Decomposition construction uses the odd inertia back property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/OddEqOneOfSubOneMem.lean#L253-L271
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/OddEqOneOfSubOneMem.lean#L253-L271

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
import Definitions.Def_Formalism_TameInertiaTowers_InvLength
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_NormalOrderTwoCentral
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_OddEqOneOfSubOneMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal
noncomputable section
open Formalism Formalism.TwoAdicCyclotomicDecomposition

theorem Formalism.TwoAdicCyclotomicDecomposition.odd_inertia_back {L : Type} [Field L] [NumberField L] [IsGalois ℚ L] {G : Type*} [One G]
    (f : Gal(L/ℚ) → G) (hinj : Function.Injective f) (h1 : f 1 = 1) (t : G)
    (r : ℕ) [Fact r.Prime] (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (span {(r : ℤ)})]
    (hfwd : ∀ τ : Gal(L/ℚ), (∀ x : 𝓞 L, τ • x - x ∈ P) → f τ = 1 ∨ f τ = t)
    (hram : P.ramificationIdx ℤ ≠ 1) (σ : Gal(L/ℚ)) (hσ : f σ = t) :
    ∀ x : 𝓞 L, σ • x - x ∈ P := by sorry
