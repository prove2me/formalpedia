-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_PrismSpan_single_mem
-- name    : Formalism.CyclotomicNorms.PrismSpan.single_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:50:49.225012+00:00
-- url     : https://prove2.me/theorems/2e87ad80-ef80-42a4-bdc4-b3e9b83fe26a
-- title:
--   Prism Span: single mem
-- statement:
--   The Prism Span construction uses the single mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/SpanQuadraticOfImage.lean#L77-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/SpanQuadraticOfImage.lean#L77-L78

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

theorem Formalism.CyclotomicNorms.PrismSpan.single_mem (i : Fin a) (w : W i) : (Pi.single i w : ∀ j, W j) ∈ coordSub ρ i := by sorry
