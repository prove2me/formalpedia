-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_classSetFinite_core
-- name    : Formalism.HermitianLatticesTheory.classSetFinite_core
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T22:31:33.876555+00:00
-- url     : https://prove2.me/theorems/6c2f687c-9220-4c10-a421-538597f8d307
-- title:
--   Hermitian Lattices Theory: class Set Finite core
-- statement:
--   The Hermitian Lattices Theory construction uses the class Set Finite core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ClassSetAssembly.lean#L708-L744
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ClassSetAssembly.lean#L708-L744

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_GenusCovolBound
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ClassSetAssembly
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

theorem Formalism.HermitianLatticesTheory.classSetFinite_core (hC : ShortVectors) (hE : FinIntermediate) (hF : IsomOfTrace)
    {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x))
    (n : ℕ) (ι : V →+ EuclideanSpace ℝ (Fin n))
    (hι : ∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ))
    (hmul : ∀ a : K, ∃ C : ℝ, ∀ x : V, ‖ι (a • x)‖ ≤ C * ‖ι x‖)
    (d : ℕ) (hd : 0 < d) (C : ℝ) (S : Set (Submodule (NumberField.RingOfIntegers K) V))
    (hSd : ∀ M ∈ S, ∀ x ∈ M, ∀ y ∈ M,
      (d : K) * h x y ∈ (1 : Submodule (NumberField.RingOfIntegers K) K))
    (hSlat : ∀ M ∈ S, ∃ _ : DiscreteTopology (zmap ι M), IsZLattice ℝ (zmap ι M))
    (hSC : ∀ M ∈ S, ∀ [DiscreteTopology (zmap ι M)] [IsZLattice ℝ (zmap ι M)],
      ZLattice.covolume (zmap ι M) ≤ C) :
    ∃ s : Finset (Submodule (NumberField.RingOfIntegers K) V), (∀ N ∈ s, N ∈ S) ∧
      ∀ M ∈ S, ∃ N ∈ s, ∃ g ∈ isom h, gmap g N = M := by sorry
