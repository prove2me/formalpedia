-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_TYPES_trace_bcRepr
-- name    : Formalism.IrreducibleCountingLemmas.TYPES.trace_bcRepr
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:33.585335+00:00
-- url     : https://prove2.me/theorems/6a7f9bc0-6625-4abf-8216-ff3e5cd199b8
-- title:
--   TYPES: trace bc Repr
-- statement:
--   The TYPES construction uses the trace bc Repr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/CentralIdempotents/GaloisConjCentralIdempotent.lean#L243-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/CentralIdempotents/GaloisConjCentralIdempotent.lean#L243-L250

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_IsConstituent
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisConjCentralIdempotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial CategoryTheory
noncomputable section
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.TYPES
variable {Γ : Type} [Group Γ]

theorem Formalism.IrreducibleCountingLemmas.TYPES.trace_bcRepr (σ : ℂ ≃+* ℂ) {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ Γ V) (γ : Γ) :
    LinearMap.trace ℂ _ (bcRepr σ ρ γ) = σ (LinearMap.trace ℂ V (ρ γ)) := by sorry
