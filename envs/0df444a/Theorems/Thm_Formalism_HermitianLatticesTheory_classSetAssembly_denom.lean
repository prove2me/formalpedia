-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_classSetAssembly_denom
-- name    : Formalism.HermitianLatticesTheory.classSetAssembly_denom
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:06:28.966914+00:00
-- url     : https://prove2.me/theorems/6e5a7b72-0d12-435c-90a3-39b9311b77a1
-- title:
--   Hermitian Lattices Theory: class Set Assembly denom
-- statement:
--   The Hermitian Lattices Theory construction uses the class Set Assembly denom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ClassSetAssembly.lean#L171-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ClassSetAssembly.lean#L171-L240

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
variable {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]

theorem Formalism.HermitianLatticesTheory.classSetAssembly_denom {n : ℕ} (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x))
    (ι : V →+ EuclideanSpace ℝ (Fin n))
    (hι : ∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ))
    (u : Fin n → V) (hu : LinearIndependent ℝ (ι ∘ u)) (d : ℕ) (hd : 0 < d)
    (hint : ∀ i j, ∃ z : ℤ, (d : ℚ) * Algebra.trace ℚ K (h (u i) (u j)) = z) :
    ∃ e : ℤ, e ≠ 0 ∧ ∀ x : V, (∀ j, ∃ z : ℤ, (d : ℚ) * Algebra.trace ℚ K (h x (u j)) = z) →
      e • x ∈ AddSubgroup.closure (Set.range u) := by sorry
