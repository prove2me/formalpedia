-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_traceReal_lower
-- name    : Formalism.HermitianLatticesTheory.traceReal_lower
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:05:33.865887+00:00
-- url     : https://prove2.me/theorems/3e134ab6-c8f8-496d-ae08-ae55f516ec7e
-- title:
--   Hermitian Lattices Theory: trace Real lower
-- statement:
--   The Hermitian Lattices Theory construction uses the trace Real lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/TraceReal.lean#L41-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/TraceReal.lean#L41-L96

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_DefsCS
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ThetaSummable
import Definitions.Def_Lemmata_GeneralBFactSecondSide_Imports
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_TraceReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
variable [Module (NumberField.RingOfIntegers K) V]
  [IsScalarTower (NumberField.RingOfIntegers K) K V]

theorem Formalism.HermitianLatticesTheory.traceReal_lower (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x))
    (L : Submodule (NumberField.RingOfIntegers K) V) [Submodule.IsLattice K L] :
    ∃ l : ℝ, 0 < l ∧ ∀ x ∈ L, x ≠ 0 → l ≤ ((Algebra.trace ℚ K (h x x) : ℚ) : ℝ) := by sorry
