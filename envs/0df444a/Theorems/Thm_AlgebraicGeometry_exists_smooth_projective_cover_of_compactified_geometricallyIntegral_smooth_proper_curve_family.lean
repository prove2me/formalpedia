-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_smooth_projective_cover_of_compactified_geometricallyIntegral_smooth_proper_curve_family
-- name    : AlgebraicGeometry.exists_smooth_projective_cover_of_compactified_geometricallyIntegral_smooth_proper_curve_family
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-26T15:05:49.410156+00:00
-- url     : https://prove2.me/theorems/aa2576df-a845-4872-804a-8685336ec20e
-- title:
--   Boundary alteration of a compactified geometrically integral smooth proper curve family
-- statement:
--   Let $K$ be algebraically closed. Let $N,G$ be normal integral proper projective $K$-schemes, with specified closed projective embeddings, and let $f:G\to N$ be a proper surjective $K$-morphism. Suppose its actual generic fibre has dimension at most one.
--
--   Let $u:U\hookrightarrow N$ be a dense integral open smooth over $K$. Suppose the whole cartesian restriction $W=G\times_N U$ is specified by a dense open immersion into $G$, and that $W\to U$ is smooth, proper, surjective, geometrically integral and geometrically connected. In particular, every geometric fibre on this open base is integral; generic geometric integrality alone is not the hypothesis.
--
--   Then there is an integral projective $K$-scheme $Y$ and a proper surjection $a:Y\to G$, with $Y$ smooth over $K$. A closed projective embedding of this same $Y$ with structure morphism exactly $a$ followed by that of $G$ is part of the conclusion.
--
--   This is the boundary extension and regularization problem after the good family has been constructed. The conclusion includes all of $Y$, including the inverse image of $N\setminus U$. The dimension-zero case is included. Stable pointed-curve extension, extension of the map to the compactification, base-boundary alteration and nodal regularization remain proof obligations of this theorem.
-- source:
--   Specialized consequence of A. J. de Jong, Smoothness, semi-stability and alterations, Publications Mathématiques de l’IHÉS 83 (1996), Theorem 4.1 and Remark 4.2, p. 66; the curve-family boundary construction is in Sections 4.17-4.26, pp. 71-75, with regularization in Proposition 3.6, pp. 64-65. https://www.numdam.org/item/PMIHES_1996__83__51_0.pdf . The additional cartesian smooth proper geometrically integral family is the prepared input for this specialized boundary step; this statement is not claimed to be a verbatim numbered theorem. A complete proof must supply stable pointed-curve extension, extension of maps, alteration of the base together with its boundary and nodal regularization, as well as the dimension-zero case. It may not import the parent frontier theorem or its ancestors.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.exists_smooth_projective_cover_of_compactified_geometricallyIntegral_smooth_proper_curve_family
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
    {U W : Scheme.{u}} [IsIntegral U] [IsIntegral W]
    (u₀ : U ⟶ N) [IsOpenImmersion u₀] [IsDominant u₀] [Smooth (u₀ ≫ πN)]
    (p : W ⟶ U) [Smooth p] [IsProper p] [Surjective p]
    [GeometricallyIntegral p] [GeometricallyConnected p]
    (t : W ⟶ G) [IsOpenImmersion t] [IsDominant t]
    (hcart : IsPullback t p f u₀)
    (hdim : ∀ η : N, IsGenericPoint η Set.univ → topologicalKrullDim (f.fiber η) ≤ 1) :
    ∃ (Y : Scheme.{u}) (a : Y ⟶ G),
      IsIntegral Y ∧ IsProper a ∧ Surjective a ∧ Smooth (a ≫ πG) ∧
      ∃ (m : ℕ) (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K)),
        IsClosedImmersion j ∧ j ≫ ProjSpace.π K m = a ≫ πG := by sorry
