-- Prove2me | Theorems.Thm_BenderSuzuki_External_huppert_II_6_11_projective_action
-- name    : BenderSuzuki.External.huppert_II_6_11_projective_action
-- status  : Proved
-- author  : @arexychen
-- created : 2026-09-12T13:44:35.43208+00:00
-- url     : https://prove2.me/theorems/f7c9fe83-4599-4ddf-af4b-1b0f5d13988b
-- title:
--   Faithful doubly transitive projective action of PSL
-- statement:
--   For a field K and n≥2, PSLₙ(K) admits a faithful permutation representation on projective (n−1)-space. It is compatible with the ordinary action of determinant-one matrices and is doubly transitive on distinct projective points. The conclusion includes the precise permutation homomorphism, injectivity, matrix compatibility and ordered-pair transitivity of Huppert II.6.11.
-- source:
--   Original formalization: Qiuzhen-CFSG/CFSG, original source authors, Apache-2.0; commit 96b2a02085dc678f3e0a97b334c31ada599c55fd; https://github.com/Qiuzhen-CFSG/CFSG/blob/96b2a02085dc678f3e0a97b334c31ada599c55fd/BenderSuzuki/External/Huppert/II/theorem_6_11.lean; declaration BenderSuzuki.External.huppert_II_6_11_projective_action. arexychen contributes extraction, target-environment replay, theorem-DAG packaging and validation, not original authorship of Dickson classification.

import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.Sylow
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Center
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.LinearAlgebra.Projectivization.Independence
set_option autoImplicit false
universe u v
open scoped Pointwise Classical
open scoped LinearAlgebra.Projectivization

theorem BenderSuzuki.External.huppert_II_6_11_projective_action
    {K : Type u} [Field K] (n : ℕ) (hn : 2 ≤ n) :
    let SL := Matrix.SpecialLinearGroup (Fin n) K
    let PSL := Matrix.ProjectiveSpecialLinearGroup (Fin n) K
    let P := ℙ K (Fin n → K)
    ∃ rho : PSL →* Equiv.Perm P,
      Function.Injective rho ∧
      (∀ (A : SL) (z : P),
        rho (QuotientGroup.mk' (Subgroup.center SL) A) z =
          (Matrix.GeneralLinearGroup.toLin
            (A : GL (Fin n) K)).toLinearEquiv • z) ∧
      (∀ a b c d : P, a ≠ b → c ≠ d →
        ∃ g : PSL, rho g a = c ∧ rho g b = d) := by sorry
