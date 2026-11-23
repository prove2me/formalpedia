-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_PrismSpan_on_diag
-- name    : Formalism.CyclotomicNorms.PrismSpan.on_diag
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:55:41.541062+00:00
-- url     : https://prove2.me/theorems/da0ab615-41ed-4e5b-8a5b-43b1144e201b
-- title:
--   Prism Span: on diag
-- statement:
--   The Prism Span construction uses the on diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/SpanQuadraticOfImage.lean#L156-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/SpanQuadraticOfImage.lean#L156-L161

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

theorem Formalism.CyclotomicNorms.PrismSpan.on_diag (hspan : ∀ i, Submodule.span k (Set.range (ρ i)) = ⊤)
    (φ : (∀ j, W j) →ₗ[alg ρ] (∀ j, W j)) (i : Fin a) (X : Module.End k (W i)) (w : W i) :
    φ (Pi.single i (X w)) i = X (φ (Pi.single i w) i) := by sorry
