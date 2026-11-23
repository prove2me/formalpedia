-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_classSetAssembly_coord_zero
-- name    : Formalism.HermitianLatticesTheory.classSetAssembly_coord_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:41:44.355971+00:00
-- url     : https://prove2.me/theorems/2b1ae1b2-a58c-40aa-b837-ae5990299812
-- title:
--   Hermitian Lattices Theory: class Set Assembly coord zero
-- statement:
--   The Hermitian Lattices Theory construction uses the class Set Assembly coord zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ClassSetAssembly.lean#L129-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ClassSetAssembly.lean#L129-L141

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

theorem Formalism.HermitianLatticesTheory.classSetAssembly_coord_zero {n : ℕ} (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x))
    (ι : V →+ EuclideanSpace ℝ (Fin n))
    (hι : ∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ))
    (u : Fin n → V) (hu : LinearIndependent ℝ (ι ∘ u)) (r : Fin n → ℚ)
    (hr : ∀ j, ∑ i, r i * Algebra.trace ℚ K (h (u i) (u j)) = 0) : r = 0 := by sorry
