-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_PrismSpan_sum_single
-- name    : Formalism.CyclotomicNorms.PrismSpan.sum_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:50:54.272949+00:00
-- url     : https://prove2.me/theorems/526a18c4-ef31-4490-99f9-ee81a472b9c2
-- title:
--   Prism Span: sum single
-- statement:
--   The Prism Span construction uses the sum single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/SpanQuadraticOfImage.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/SpanQuadraticOfImage.lean#L11-L13

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

theorem Formalism.CyclotomicNorms.PrismSpan.sum_single {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type}
    [∀ i, AddCommMonoid (X i)] (v : ∀ i, X i) : ∑ i, Pi.single i (v i) = v := by sorry
