-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_mem_of_repr_ne_zero
-- name    : Formalism.CyclotomicNorms.mem_of_repr_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:57:47.238807+00:00
-- url     : https://prove2.me/theorems/594f9474-868e-4af6-a230-b7b4dd6bff63
-- title:
--   Cyclotomic Norms: mem of repr ne zero
-- statement:
--   The Cyclotomic Norms construction uses the mem of repr ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/RestrictionOfBlocksAndJordan.lean#L45-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/RestrictionOfBlocksAndJordan.lean#L45-L86

import Definitions.Def_Formalism_CyclotomicNorms_StatementI
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_PowerPCycle
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_RestrictionOfBlocksAndJordan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module
noncomputable section
open Formalism Formalism.CyclotomicNorms
variable {G k V : Type} [Group G] [Field k] [AddCommGroup V] [Module k V] {N : ℕ}

theorem Formalism.CyclotomicNorms.mem_of_repr_ne_zero (ρ : Representation k G V) (e : Module.Basis (Fin N) k V)
    (χ : Fin N → G → k) (I : Subgroup G) (he : ∀ i, ∀ y ∈ I, ρ y (e i) = χ i y • e i)
    (hsep : ∀ i j, i ≠ j → ∃ y ∈ I, χ i y ≠ χ j y) (W : Submodule k V)
    (hW : ∀ y ∈ I, ∀ x ∈ W, ρ y x ∈ W) :
    ∀ w ∈ W, ∀ i, e.repr w i ≠ 0 → e i ∈ W := by sorry
