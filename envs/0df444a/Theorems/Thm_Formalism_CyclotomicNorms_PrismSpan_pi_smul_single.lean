-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_PrismSpan_pi_smul_single
-- name    : Formalism.CyclotomicNorms.PrismSpan.pi_smul_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:04:39.749696+00:00
-- url     : https://prove2.me/theorems/170fdd18-2c7c-4d0d-ab45-41fa5a6cb780
-- title:
--   Prism Span: pi smul single
-- statement:
--   The Prism Span construction uses the pi smul single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/SpanQuadraticOfImage.lean#L31-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/SpanQuadraticOfImage.lean#L31-L37

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

theorem Formalism.CyclotomicNorms.PrismSpan.pi_smul_single (E : ∀ j, Module.End k (W j)) (i : Fin a) (w : W i) :
    E • (Pi.single i w : ∀ j, W j) = Pi.single i (E i w) := by sorry
