-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_FS_PLat_proj
-- name    : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS.PLat.proj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:14:17.411103+00:00
-- url     : https://prove2.me/theorems/e9b301eb-03c6-404e-a79b-0eaafbc2b0b7
-- title:
--   PLat: proj
-- statement:
--   The PLat construction uses the proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/PUnitBasis.lean#L38-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/PUnitBasis.lean#L38-L74

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_PFourSq
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_PUnitBasis
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

theorem Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS.PLat.proj (P : PLat c h O L p) {ι : Type} [Fintype ι] [DecidableEq ι] {v : ι → V} {n : ι → ℕ}
    (G : Good h L p v n) (x : V) (hx : x ∈ L) :
    ∃ x' ∈ L, (∀ j, h x' (v j) = 0) ∧ ∃ N : ℕ, Nat.Coprime N p ∧ N ≠ 0 ∧
      ((N : K) • x - x' ∈ Submodule.span K (Set.range v)) ∧
      ∀ y, (∀ i, h y (v i) = 0) → h x' y = (N : K) * h x y := by sorry
