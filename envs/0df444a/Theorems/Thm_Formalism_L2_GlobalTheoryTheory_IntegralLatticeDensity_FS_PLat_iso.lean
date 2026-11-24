-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_FS_PLat_iso
-- name    : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS.PLat.iso
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:49:40.822298+00:00
-- url     : https://prove2.me/theorems/e6f9c97c-72e3-4514-b8aa-e838528a0e69
-- title:
--   PLat: iso
-- statement:
--   The PLat construction uses the iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/PUnitBasis.lean#L232-L282
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/PUnitBasis.lean#L232-L282

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_PFourSq
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_PUnitBasis
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_FS_Herm4_iso

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Module
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS
variable {K : Type} [Field K] [CharZero K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {c : K →+* K} {h : V → V → K} {O : Subring K} {L : AddSubgroup V} {p : ℕ}

theorem Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS.PLat.iso (P : PLat c h O L p) {ι : Type} [Fintype ι] [DecidableEq ι] (hι : Fintype.card ι = finrank K V) :
    ∃ g : (Fin 4 → V) ≃ₗ[K] (Fin 4 × ι → K), (∀ x y, ∑ w, g x w * c (g y w) = ∑ a, h (x a) (y a)) ∧
      ∃ s : ℕ, Nat.Coprime s p ∧ (∀ x : Fin 4 → V, (∀ a, x a ∈ L) → ∀ w, (s : K) * g x w ∈ O) ∧
        ∀ u : Fin 4 × ι → K, (∀ w, u w ∈ O) → ∀ a, (s : K) • g.symm u a ∈ L := by sorry
