-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_classSetAssembly_min
-- name    : Formalism.HermitianLatticesTheory.classSetAssembly_min
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:06:50.388598+00:00
-- url     : https://prove2.me/theorems/f7162eee-7e1a-427b-ae0d-afefe696ca5b
-- title:
--   Hermitian Lattices Theory: class Set Assembly min
-- statement:
--   The Hermitian Lattices Theory construction uses the class Set Assembly min property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ClassSetAssembly.lean#L518-L548
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ClassSetAssembly.lean#L518-L548

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

theorem Formalism.HermitianLatticesTheory.classSetAssembly_min {n : ℕ} (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x))
    (ι : V →+ EuclideanSpace ℝ (Fin n))
    (hι : ∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ))
    (d : ℕ) (hd : 0 < d) (M : Submodule (NumberField.RingOfIntegers K) V)
    (hdM : ∀ x ∈ M, ∀ y ∈ M, (d : K) * h x y ∈ (1 : Submodule (NumberField.RingOfIntegers K) K))
    (x : V) (hx : x ∈ M) (hx0 : x ≠ 0) : 1 / (d : ℝ) ≤ ‖ι x‖ := by sorry
