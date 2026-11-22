-- Prove2me | Theorems.Thm_Formalism_NG_QuotientPowerLengths_congMod_le
-- name    : Formalism.NG.QuotientPowerLengths.congMod_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T18:36:42.651748+00:00
-- url     : https://prove2.me/theorems/1114379d-1aa2-47f0-a5b4-423c484f8d3c
-- title:
--   Quotient Power Lengths: cong Mod le
-- statement:
--   The Quotient Power Lengths construction uses the cong Mod le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthQuotSmulRangeFree.lean#L559-L582
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthQuotSmulRangeFree.lean#L559-L582

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
variable {X : Type*} {T : Subalgebra O (X → O)} {act : T →+* Module.End (FractionRing O) V}

theorem Formalism.NG.QuotientPowerLengths.congMod_le (hsum : (⨆ x, Vx T act x) = ⊤) (L : Submodule O V) (hL : L.FG)
    (S : Finset X) (E : Set (Module.End (FractionRing O) V)) (w : X → ℕ∞)
    (hcomm : ∀ g ∈ E, ∀ f : T, g * act f = act f * g)
    (hEL : ∀ g ∈ E, ∀ v ∈ L, g v ∈ L) (hES : ∀ g ∈ E, ∀ v ∈ L, g v ∈ VS T act (S : Set X))
    (hmin : ∀ x ∈ S, ∃ g ∈ E, ∃ l : O, (∀ v ∈ Vx T act x, g v = l • v) ∧ addVal O l ≤ w x) :
    Module.length O (CongMod T act L (S : Set X)) ≤
      ∑ x ∈ S, (finrank (FractionRing O) (Vx T act x) : ℕ∞) * w x := by sorry
