-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_PrismSpan_off_diag
-- name    : Formalism.CyclotomicNorms.PrismSpan.off_diag
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:55:38.615145+00:00
-- url     : https://prove2.me/theorems/37f5c103-c6a1-4b02-b12e-266a5cd0e734
-- title:
--   Prism Span: off diag
-- statement:
--   The Prism Span construction uses the off diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/SpanQuadraticOfImage.lean#L121-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/SpanQuadraticOfImage.lean#L121-L154

import Definitions.Def_Formalism_CyclotomicNorms_StatementA
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_SpanQuadraticOfImage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module
open Formalism Formalism.CyclotomicNorms
open Formalism.CyclotomicNorms.PrismSpan
variable {k G : Type} [Field k] [Group G] {a : ℕ} {W : Fin a → Type}
  [∀ i, AddCommGroup (W i)] [∀ i, Module k (W i)]
variable (ρ : ∀ i, Representation k G (W i))
variable {ρ}

theorem Formalism.CyclotomicNorms.PrismSpan.off_diag (hspan : ∀ i, Submodule.span k (Set.range (ρ i)) = ⊤)
    (hne : ∀ i j, i ≠ j → ¬ ∃ T : W i ≃ₗ[k] W j, ∀ g x, T (ρ i g x) = ρ j g (T x))
    (φ : (∀ j, W j) →ₗ[alg ρ] (∀ j, W j)) {i j : Fin a} (hij : i ≠ j) (w : W i) :
    φ (Pi.single i w) j = 0 := by sorry
