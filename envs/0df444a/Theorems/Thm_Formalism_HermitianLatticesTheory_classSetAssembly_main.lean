-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_classSetAssembly_main
-- name    : Formalism.HermitianLatticesTheory.classSetAssembly_main
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:18.424445+00:00
-- url     : https://prove2.me/theorems/6696562a-3174-4218-b2ab-cf4e4fc261b8
-- title:
--   Hermitian Lattices Theory: class Set Assembly main
-- statement:
--   The Hermitian Lattices Theory construction uses the class Set Assembly main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ClassSetAssembly.lean#L558-L704
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ClassSetAssembly.lean#L558-L704

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
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]

theorem Formalism.HermitianLatticesTheory.classSetAssembly_main (hE : FinIntermediate) (hF : IsomOfTrace)
    (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x))
    {n : ℕ} (ι : V →+ EuclideanSpace ℝ (Fin n))
    (hι : ∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ))
    (hmul : ∀ a : K, ∃ C : ℝ, ∀ x : V, ‖ι (a • x)‖ ≤ C * ‖ι x‖)
    (d : ℕ) (hd : 0 < d) (S : Set (Submodule (NumberField.RingOfIntegers K) V))
    (hdM : ∀ M ∈ S, ∀ x ∈ M, ∀ y ∈ M,
      (d : K) * h x y ∈ (1 : Submodule (NumberField.RingOfIntegers K) K))
    (B : ℝ)
    (hgood : ∀ M ∈ S, ∃ u : Fin n → V, (∀ i, u i ∈ M) ∧ LinearIndependent ℝ (ι ∘ u) ∧
      ∀ i, ‖ι (u i)‖ ≤ B) :
    ∃ s : Finset (Submodule (NumberField.RingOfIntegers K) V), (∀ M ∈ s, M ∈ S) ∧
      ∀ M ∈ S, ∃ N ∈ s, ∃ g ∈ isom h, gmap g N = M := by sorry
