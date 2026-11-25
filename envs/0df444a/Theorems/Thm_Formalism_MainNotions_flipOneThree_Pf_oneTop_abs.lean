-- Prove2me | Theorems.Thm_Formalism_MainNotions_flipOneThree_Pf_oneTop_abs
-- name    : Formalism.MainNotions.flipOneThree.Pf.oneTop_abs
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:12:36.590284+00:00
-- url     : https://prove2.me/theorems/be031c05-9aa0-446e-81e8-e3e50a635755
-- title:
--   Pf: one Top abs
-- statement:
--   The Pf construction uses the one Top abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/ColumnSpanDensity/HarProjEqZeroIff.lean#L87-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/ColumnSpanDensity/HarProjEqZeroIff.lean#L87-L224

import Definitions.Def_Formalism_PolynomialDimension_FinalHar
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_HarProjEqZeroIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.flipOneThree Formalism.MainNotions.flipOneThree.Pf
open Formalism.CountingSumsFrames MvPolynomial

theorem Formalism.MainNotions.flipOneThree.Pf.oneTop_abs (K : Type) [Field K] [CharZero K] (k P Q p : ℕ) (hk : 1 ≤ k) (hp : p.Prime)
    (Ov : ValuationSubring K) (hloc : PLocal Ov.toSubring p)
    {V2 : Type} [AddCommGroup V2] [Module K V2] (α : V2 ≃ₗ[K] PolAB K k P Q)
    (W : ℕ → Type) [∀ j, AddCommGroup (W j)] [∀ j, Module K (W j)]
    (β : ∀ j, PolAB K k (P - j) (Q - j) →ₗ[K] W j) (hsurj : ∀ j, Function.Surjective (β j))
    (hker : ∀ j (f : PolAB K k (P - j) (Q - j)), β j f = 0 ↔
      ∃ G ∈ PolAB K k (P - j - 1) (Q - j - 1), (f : PolXY K k) = hXY K k * G) :
    ∃ (io : ∀ j, W j →ₗ[K] V2) (pr : ∀ j, V2 →ₗ[K] W j),
      (∀ x, ∑ j ∈ Finset.range (min P Q + 1), io j (pr j x) = x) ∧
      ∀ (g : GL (Fin k) K) (j : ℕ), j ≤ min P Q →
        (∀ x, (α x : PolXY K k) ∈ latOf g (GaussLat Ov.toSubring) →
          ∃ f : PolAB K k (P - j) (Q - j), (f : PolXY K k) ∈ latOf g (GaussLat Ov.toSubring) ∧
            β j f = ((p : K) ^ ((k + 1) * Nat.log p (P + Q + k))) • pr j x) ∧
        (∀ f : PolAB K k (P - j) (Q - j), (f : PolXY K k) ∈ latOf g (GaussLat Ov.toSubring) →
          (α (((p : K) ^ ((k + 1) * Nat.log p (P + Q + k))) • io j (β j f)) : PolXY K k) ∈
            latOf g (GaussLat Ov.toSubring)) := by sorry
