-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_normal_projective_alteration_with_geometricallyIntegral_smooth_proper_generic_curve
-- name    : AlgebraicGeometry.exists_normal_projective_alteration_with_geometricallyIntegral_smooth_proper_generic_curve
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-26T02:39:48.074051+00:00
-- url     : https://prove2.me/theorems/fdd30f1a-b4bd-4bf7-9647-e2b0056ba8b8
-- title:
--   A normal projective alteration with geometrically integral smooth proper generic curve
-- statement:
--   Let $k$ be a perfect field. Let $S,X$ be integral proper projective $k$-schemes with specified projective embeddings, and let $q:X\to S$ be a proper dominant $k$-morphism. Suppose $\dim S=r$ and $\dim X=r+1$ for an integer $r\geq0$.
--
--   There are normal integral projective $k$-schemes $N,G$ with proper surjections $q_N:N\to S$, $f_X:G\to X$ and $f_N:G\to N$, satisfying
--   $$\dim N=\dim S,\qquad \dim G=\dim X,\qquad q\circ f_X=q_N\circ f_N.$$
--   The actual generic fibre of $f_X$ is finite over the residue field of the generic point of $X$.
--
--   For every actual generic point $\eta_N$ of $N$, the fibre $G_{\eta_N}$ is a geometrically integral, geometrically connected, smooth proper curve of dimension exactly one over $\kappa(\eta_N)$.
--
--   There is a dense integral open $u:U\hookrightarrow N$ smooth over $k$, and an integral smooth proper surjective family $p_W:W\to U$. A specified dense open immersion $t_W:W\hookrightarrow G$ identifies the whole family with the actual restriction $G\times_N U$, and $W$ is smooth over $k$. Both global maps have the same $k$-structure. Projective embeddings of the same $N$ and $G$ and their exact structure equations are retained, as is $\dim G=\dim W$.
--
--   This supplies a dimension-preserving normal alteration with a geometrically integral generic curve. The global total space is normal; extension and regularization across the remaining boundary are further assertions.
-- source:
--   Refinement of the Philippon boundary-alteration frontier https://prove2.me/theorems/2b22e38e-7ad7-446f-96fe-a271d21ea8d3 , building on the accepted finite-field geometrically integral curve cover https://prove2.me/theorems/c413d547-014f-459d-aad9-d5914f26f9c0 and normal projective family completion https://prove2.me/theorems/77bad564-392b-4202-9bf6-e267f19ec58c . The source and its generic morphism are spread independently, preserving dominance over the original variety. Geometric integrality is transported through the actual canonical residue-field comparison and the surjective open source subfamily. The dimension argument is the established generic-fibre transcendence-degree calculation. Compare de Jong, Smoothness, semi-stability and alterations (1996), Sections 4.11-4.17, https://www.numdam.org/item/PMIHES_1996__83__51_0.pdf . No semistable extension or global smooth alteration is assumed.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.exists_normal_projective_alteration_with_geometricallyIntegral_smooth_proper_generic_curve
    (k : Type u) [Field k] [PerfectField k] {S X : Scheme.{u}} [IsIntegral S] [IsIntegral X]
    (πS : S ⟶ Spec (.of k)) [IsProper πS]
    (mS : ℕ) (iS : S ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (mS + 1)) k))
    [IsClosedImmersion iS] (hiS : iS ≫ ProjSpace.π k mS = πS)
    (πX : X ⟶ Spec (.of k)) [IsProper πX]
    (mX : ℕ) (iX : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (mX + 1)) k))
    [IsClosedImmersion iX] (hiX : iX ≫ ProjSpace.π k mX = πX)
    (q : X ⟶ S) [IsProper q] [IsDominant q] (hqπ : q ≫ πS = πX)
    (r : ℕ) (hdS : topologicalKrullDim S = (r : WithBot ℕ∞))
    (hdX : topologicalKrullDim X = ((r + 1 : ℕ) : WithBot ℕ∞)) :
    ∃ (N : Scheme.{u}) (qN : N ⟶ S) (U : Scheme.{u}) (u : U ⟶ N)
      (W : Scheme.{u}) (pW : W ⟶ U) (G : Scheme.{u})
      (fX : G ⟶ X) (fN : G ⟶ N) (tW : W ⟶ G),
      IsIntegral N ∧ (∀ x : N, IsIntegrallyClosed (N.presheaf.stalk x)) ∧
      IsProper qN ∧ Surjective qN ∧ topologicalKrullDim N = topologicalKrullDim S ∧
      IsIntegral U ∧ IsOpenImmersion u ∧ IsDominant u ∧ Smooth (u ≫ qN ≫ πS) ∧
      IsIntegral W ∧ Smooth pW ∧ IsProper pW ∧ Surjective pW ∧
      Smooth (pW ≫ u ≫ qN ≫ πS) ∧
      IsIntegral G ∧ (∀ x : G, IsIntegrallyClosed (G.presheaf.stalk x)) ∧
      IsProper fX ∧ Surjective fX ∧ topologicalKrullDim G = topologicalKrullDim X ∧
      IsFinite (fX.fiberToSpecResidueField (genericPoint X)) ∧
      IsProper fN ∧ Surjective fN ∧
      IsOpenImmersion tW ∧ IsDominant tW ∧ IsPullback tW pW fN u ∧
      (∀ ηN : N, IsGenericPoint ηN Set.univ →
        IsIntegral (fN.fiber ηN) ∧ Smooth (fN.fiberToSpecResidueField ηN) ∧
        IsProper (fN.fiberToSpecResidueField ηN) ∧
        GeometricallyIntegral (fN.fiberToSpecResidueField ηN) ∧
        GeometricallyConnected (fN.fiberToSpecResidueField ηN) ∧ topologicalKrullDim (fN.fiber ηN) = 1) ∧
      fX ≫ q = fN ≫ qN ∧ fX ≫ πX = fN ≫ qN ≫ πS ∧
      topologicalKrullDim G = topologicalKrullDim W ∧
      (∃ (dN : ℕ) (jN : N ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (dN + 1)) k)),
        IsClosedImmersion jN ∧ jN ≫ ProjSpace.π k dN = qN ≫ πS) ∧
      ∃ (dG : ℕ) (jG : G ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (dG + 1)) k)),
        IsClosedImmersion jG ∧ jG ≫ ProjSpace.π k dG = fX ≫ πX := by sorry
