-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_PrismSpan_alg_smul_eq
-- name    : Formalism.CyclotomicNorms.PrismSpan.alg_smul_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:55:21.704319+00:00
-- url     : https://prove2.me/theorems/47bf6692-6ec5-4143-b2f6-e87cbe4a633c
-- title:
--   Prism Span: alg smul eq
-- statement:
--   The Prism Span construction uses the alg smul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/SpanQuadraticOfImage.lean#L39-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/SpanQuadraticOfImage.lean#L39-L42

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

theorem Formalism.CyclotomicNorms.PrismSpan.alg_smul_eq (c : k) (m : ∀ i, W i) : (algebraMap k (alg ρ) c) • m = c • m := by sorry
