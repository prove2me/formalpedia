-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_classSetAssembly_exists_isom
-- name    : Formalism.HermitianLatticesTheory.classSetAssembly_exists_isom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:06:36.153634+00:00
-- url     : https://prove2.me/theorems/f17cb3be-b91f-4b5b-b603-27499b2b5989
-- title:
--   Hermitian Lattices Theory: class Set Assembly exists isom
-- statement:
--   The Hermitian Lattices Theory construction uses the class Set Assembly exists isom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ClassSetAssembly.lean#L474-L504
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ClassSetAssembly.lean#L474-L504

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

theorem Formalism.HermitianLatticesTheory.classSetAssembly_exists_isom {n : ℕ} (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x))
    (ι : V →+ EuclideanSpace ℝ (Fin n))
    (hι : ∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ))
    {κ : Type*} [Fintype κ] (ω : Basis κ ℚ K)
    (u u' : Fin n → V) (hu : LinearIndependent ℝ (ι ∘ u)) (hu' : LinearIndependent ℝ (ι ∘ u'))
    (hG : ∀ i l, Algebra.trace ℚ K (h (u i) (u l)) = Algebra.trace ℚ K (h (u' i) (u' l)))
    (hA : ∀ k i l, Algebra.trace ℚ K (h (ω k • u i) (u l)) =
      Algebra.trace ℚ K (h (ω k • u' i) (u' l))) :
    ∃ φ : V ≃ₗ[K] V, (∀ x y, Algebra.trace ℚ K (h (φ x) (φ y)) = Algebra.trace ℚ K (h x y)) ∧
      ∀ i, φ (u i) = u' i := by sorry
