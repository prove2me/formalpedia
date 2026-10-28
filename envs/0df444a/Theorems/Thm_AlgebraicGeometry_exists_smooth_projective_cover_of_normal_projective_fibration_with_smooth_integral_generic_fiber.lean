-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_smooth_projective_cover_of_normal_projective_fibration_with_smooth_integral_generic_fiber
-- name    : AlgebraicGeometry.exists_smooth_projective_cover_of_normal_projective_fibration_with_smooth_integral_generic_fiber
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-26T00:55:49.244454+00:00
-- url     : https://prove2.me/theorems/2b22e38e-7ad7-446f-96fe-a271d21ea8d3
-- title:
--   Boundary alteration for a normal projective fibration with smooth integral generic curve
-- statement:
--   Let $K$ be algebraically closed. Let $N$ and $G$ be normal integral proper projective $K$-schemes with specified projective embeddings, and let $f:G\to N$ be a proper surjective $K$-morphism. Suppose the actual generic fibre of $f$ is integral, smooth and proper over the residue field of the generic point, with dimension at most one.
--
--   Then there is an integral smooth projective $K$-scheme $Y$ with a proper surjection $a:Y\to G$. The same $Y$ has a specified closed projective embedding with structure morphism exactly $a$ followed by the given structure map of $G$.
--
--   This is the remaining boundary-alteration step after constructing a normal projective model with controlled smooth generic curve. Smoothness is required on all of $Y$. Merely choosing a smooth dense source open, or a normal projective completion, does not prove the conclusion. No geometric connectedness of the given generic fibre is assumed.
-- source:
--   A focused generic-curve case of A. J. de Jong, Smoothness, semi-stability and alterations (1996), Sections 3 and 4, https://www.numdam.org/item/PMIHES_1996__83__51_0.pdf . The remaining argument involves stable pointed-curve extension after alteration of the base, extension of the map to the original model, alteration of the base together with its degeneration divisor, and resolution of the resulting nodal local equations. These steps, including any necessary finite constant-field extension and dimension-zero case, remain explicit proof obligations. This theorem is not supplied by the accepted normal projective family-completion or generic-fibre comparison results.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.exists_smooth_projective_cover_of_normal_projective_fibration_with_smooth_integral_generic_fiber
    (K : Type u) [Field K] [IsAlgClosed K] {N G : Scheme.{u}}
    [IsIntegral N] [IsIntegral G]
    (πN : N ⟶ Spec (.of K)) [IsProper πN]
    (dN : ℕ) (iN : N ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (dN + 1)) K))
    [IsClosedImmersion iN] (hiN : iN ≫ ProjSpace.π K dN = πN)
    (πG : G ⟶ Spec (.of K)) [IsProper πG]
    (dG : ℕ) (iG : G ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (dG + 1)) K))
    [IsClosedImmersion iG] (hiG : iG ≫ ProjSpace.π K dG = πG)
    (f : G ⟶ N) [IsProper f] [Surjective f] (hf : f ≫ πN = πG)
    (hnN : ∀ x : N, IsIntegrallyClosed (N.presheaf.stalk x))
    (hnG : ∀ x : G, IsIntegrallyClosed (G.presheaf.stalk x))
    (hgeneric : ∀ η : N, IsGenericPoint η Set.univ →
      IsIntegral (f.fiber η) ∧ Smooth (f.fiberToSpecResidueField η) ∧
      IsProper (f.fiberToSpecResidueField η) ∧ topologicalKrullDim (f.fiber η) ≤ 1) :
    ∃ (Y : Scheme.{u}) (a : Y ⟶ G),
      IsIntegral Y ∧ IsProper a ∧ Surjective a ∧ Smooth (a ≫ πG) ∧
      ∃ (m : ℕ) (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K)),
        IsClosedImmersion j ∧ j ≫ ProjSpace.π K m = a ≫ πG := by sorry
