-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_FS_PLat_zero_of_div
-- name    : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS.PLat.zero_of_div
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:57:55.406408+00:00
-- url     : https://prove2.me/theorems/6701cb39-8203-4498-ae78-66a5b36e9dc3
-- title:
--   PLat: zero of div
-- statement:
--   The PLat construction uses the zero of div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/PUnitBasis.lean#L117-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/PUnitBasis.lean#L117-L148

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
variable (P : PLat c h O L p) {ι : Type} [Fintype ι] [DecidableEq ι] {v : ι → V} {n : ι → ℕ} (G : Good h L p v n)
  (hdiv : ∀ y ∈ L, (∀ i, h y (v i) = 0) → ∃ k : ℕ, h y y = (p : K) * k)
include P G hdiv

theorem Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS.PLat.zero_of_div : ∀ (m : ℕ) (y : V), y ∈ L → (∀ i, h y (v i) = 0) → h y y = (m : K) → y = 0 := by sorry
