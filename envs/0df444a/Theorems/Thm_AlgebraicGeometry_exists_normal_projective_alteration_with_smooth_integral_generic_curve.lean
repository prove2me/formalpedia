-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_normal_projective_alteration_with_smooth_integral_generic_curve
-- name    : AlgebraicGeometry.exists_normal_projective_alteration_with_smooth_integral_generic_curve
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-26T01:22:18.545641+00:00
-- url     : https://prove2.me/theorems/030d9618-bc42-463b-a23d-5c6d040f9460
-- title:
--   A dimension-preserving normal projective alteration with smooth integral generic curve
-- statement:
--   Let $k$ be a perfect field, and let $S,X$ be integral proper projective $k$-schemes with specified projective embeddings. Let $q:X\to S$ be a proper dominant $k$-morphism. Suppose $\dim S=r$ and $\dim X=r+1$ for an integer $r\geq0$.
--
--   There exist normal integral projective $k$-schemes $N,G$ and proper surjections $q_N:N\to S$, $f_X:G\to X$ and $f_N:G\to N$ such that
--   $$\dim N=\dim S,\qquad \dim G=\dim X,\qquad q\circ f_X=q_N\circ f_N.$$
--   The actual generic fibre of $f_X$ is finite over the residue field of the generic point of $X$. Thus $f_X$ is a dimension-preserving projective alteration of $X$.
--
--   For every actual generic point $\eta_N$ of $N$, the fibre $G_{\eta_N}$ is integral, smooth and proper over $\kappa(\eta_N)$ and has dimension exactly one. There is a dense integral open $u:U\hookrightarrow N$ smooth over $k$, and an integral smooth proper surjective family $p_W:W\to U$. A specified dense open immersion $t_W:W\hookrightarrow G$ identifies this entire family with $G\times_N U$; $W$ is smooth over $k$.
--
--   Both global maps have the same $k$-structure. The projective embeddings of the same $N$ and $G$, with their exact structure equations, are retained, as is $\dim G=\dim W$. The total space $G$ is normal; smoothness across its remaining boundary is a separate assertion.
-- source:
--   Strengthens the accepted controlled generic-curve model https://prove2.me/theorems/5f37d30e-bf3b-4bbf-ae00-2dff4bdf0d23 by proving dimension preservation and finiteness of the actual generic fibre of the map to the original variety. The dimension proof reuses the already established residue-field/transcendence-degree tower calculation and the Proved residue dimension theorem https://prove2.me/theorems/55a96175-21ad-5289-9c25-56ba81f78722 . Compare Stacks Project, dimension of fibres, https://stacks.math.columbia.edu/tag/02FW , and de Jong, Smoothness, semi-stability and alterations (1996), Sections 4.11-4.12, https://www.numdam.org/item/PMIHES_1996__83__51_0.pdf . This supplies dimension control for the induction; it does not assume or prove the remaining boundary alteration https://prove2.me/theorems/2b22e38e-7ad7-446f-96fe-a271d21ea8d3 .

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.exists_normal_projective_alteration_with_smooth_integral_generic_curve
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
        IsProper (fN.fiberToSpecResidueField ηN) ∧ topologicalKrullDim (fN.fiber ηN) = 1) ∧
      fX ≫ q = fN ≫ qN ∧ fX ≫ πX = fN ≫ qN ≫ πS ∧
      topologicalKrullDim G = topologicalKrullDim W ∧
      (∃ (dN : ℕ) (jN : N ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (dN + 1)) k)),
        IsClosedImmersion jN ∧ jN ≫ ProjSpace.π k dN = qN ≫ πS) ∧
      ∃ (dG : ℕ) (jG : G ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (dG + 1)) k)),
        IsClosedImmersion jG ∧ jG ≫ ProjSpace.π k dG = fX ≫ πX := by sorry
