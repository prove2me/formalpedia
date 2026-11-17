-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_pointProjectivization_eq_mk_comp_of_sections_eq
-- name    : AlgebraicGeometry.Scheme.Modules.ProjPresentation.pointProjectivization_eq_mk_comp_of_sections_eq
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:14:05.362812+00:00
-- url     : https://prove2.me/theorems/3d9b1889-9b35-4cfa-8af9-c87046ce0ed2
-- title:
--   A matched subfamily of coordinates represents the first projectivization
-- statement:
--   Under the section-matching and chart-inclusion hypotheses for presentations $P_1$ and $P_2$, let a nonzero vector $v$ represent $P_2(x)$ at a rational point $x$. Then $v∘inc$ is nonzero and $$P_1(x)=[v∘inc].$$ This extracts the projective coordinates of the smaller presentation from the larger one.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjPresentationHeight

set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.ProjPresentation

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.pointProjectivization_eq_mk_comp_of_sections_eq {K : Type} [Field K]
    {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of K)}
    {M₁ M₂ : X.Modules} {N₁ N₂ : ℕ}
    (P₁ : M₁.ProjPresentation f N₁) (P₂ : M₂.ProjPresentation f N₂)
    (e : M₁ ≅ M₂) (inc : Fin (N₁ + 1) → Fin (N₂ + 1))
    (hσ : ∀ i, e.hom.app ⊤ (P₁.σ i) = P₂.σ (inc i))
    (hU : ∀ i, P₁.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X i) ≤
      P₂.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X (inc i)))
    (x : Scheme.KPoint f) (v : Fin (N₂ + 1) → K) (hv : v ≠ 0)
    (hvpoint : (ProjSpace.kPointOfVec K N₂ v hv).1 = x.1 ≫ P₂.toProj) :
    ∃ hinc : v ∘ inc ≠ 0,
      P₁.pointProjectivization x = Projectivization.mk K (v ∘ inc) hinc := by sorry
