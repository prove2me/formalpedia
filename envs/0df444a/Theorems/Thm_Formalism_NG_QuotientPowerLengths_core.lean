-- Prove2me | Theorems.Thm_Formalism_NG_QuotientPowerLengths_core
-- name    : Formalism.NG.QuotientPowerLengths.core
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:13:54.22617+00:00
-- url     : https://prove2.me/theorems/8e21565f-5de4-45bc-bfe2-deaf90c4c16d
-- title:
--   Quotient Power Lengths: core
-- statement:
--   The Quotient Power Lengths construction uses the core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthQuotSmulRangeFree.lean#L351-L482
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthQuotSmulRangeFree.lean#L351-L482

import Definitions.Def_Formalism_CharacterColumnKernels_StatementN
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LenCokerOfDetNeZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthQuotSmulRangeFree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDiscreteValuationRing
noncomputable section
open Formalism Formalism.NG
open Formalism.NG.QuotientPowerLengths
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {V : Type*} [AddCommGroup V] [Module (FractionRing O) V] [Module O V]
  [IsScalarTower O (FractionRing O) V] [FiniteDimensional (FractionRing O) V]

theorem Formalism.NG.QuotientPowerLengths.core {X : Type*} (E : Set (Module.End (FractionRing O) V))
    (W : X → Submodule (FractionRing O) V) (w : X → ℕ∞) (S : Finset X) :
    (∀ f ∈ E, ∀ x ∈ S, W x ≤ (W x).comap f) →
    (∀ x ∈ S, ∃ f ∈ E, ∃ l : O, (∀ v ∈ W x, f v = l • v) ∧ addVal O l ≤ w x) →
    ∀ U : Submodule (FractionRing O) V, (∀ f ∈ E, U ≤ U.comap f) →
    ∀ N : Submodule O V, N.FG → (∀ f ∈ E, ∀ n ∈ N, f n ∈ N) →
    N ≤ ((⨆ x ∈ S, W x) ⊔ U).restrictScalars O →
    Module.length O (N ⧸ Dsub E N U) ≤ ∑ x ∈ S, (finrank (FractionRing O) (W x) : ℕ∞) * w x := by sorry
