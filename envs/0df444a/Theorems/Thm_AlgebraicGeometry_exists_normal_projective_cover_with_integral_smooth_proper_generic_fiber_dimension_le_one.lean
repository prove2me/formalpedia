-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_normal_projective_cover_with_integral_smooth_proper_generic_fiber_dimension_le_one
-- name    : AlgebraicGeometry.exists_normal_projective_cover_with_integral_smooth_proper_generic_fiber_dimension_le_one
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-26T00:38:20.720978+00:00
-- url     : https://prove2.me/theorems/5f37d30e-bf3b-4bbf-ae00-2dff4bdf0d23
-- title:
--   A normal projective cover with an integral smooth proper generic curve
-- statement:
--   Let $k$ be a perfect field, and let $S,X$ be integral proper projective $k$-schemes with specified projective embeddings. Let $q:X\to S$ be a proper dominant $k$-morphism. For the actual generic point $\eta$ of $S$, assume $\dim X_\eta\leq1$.
--
--   There exist a normal integral projective $k$-scheme $N$, a proper surjection $q_N:N\to S$ with $\dim N=\dim S$, and a dense integral open $u:U\hookrightarrow N$ smooth over $k$. There are also an integral scheme $W$, a smooth proper surjection $p_W:W\to U$, and a normal integral projective $k$-scheme $G$ with proper surjections $f_X:G\to X$ and $f_N:G\to N$ such that
--   $$q\circ f_X=q_N\circ f_N.$$
--   A specified dense open immersion $t_W:W\hookrightarrow G$ exhibits an actual cartesian square $W\simeq G\times_N U$. The total space $W$ is smooth over $k$.
--
--   For every actual generic point $\eta_N$ of $N$, the fibre $G_{\eta_N}$ is integral, smooth and proper over $\kappa(\eta_N)$ and has dimension at most one. Both global maps have the same $k$-structure. The projective embeddings of this same $N$ and $G$ and their exact structure equations are retained, as is $\dim G=\dim W$.
--
--   This gives a global normal projective model with a controlled generic fibre and its whole smooth proper restriction. Smoothness over the remaining boundary is a further step.
-- source:
--   A contribution to the Philippon curve-fibration alteration frontier https://prove2.me/theorems/842dbd70-6333-40fa-86df-02394eb67249 . Strengthens the accepted global family model by retaining the prescribed actual generic source through dense-open restriction and integral component selection. Uses the accepted canonical generic-fibre dimension comparison https://prove2.me/theorems/f97c766d-5c75-4daf-81e8-adb9942be388 , actual finite-base covering data, normal projective family completion, and generic-fibre integrality. Smoothness descends along the actual residue-field extension. No global smooth alteration is assumed or concluded.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.exists_normal_projective_cover_with_integral_smooth_proper_generic_fiber_dimension_le_one
    (k : Type u) [Field k] [PerfectField k] {S X : Scheme.{u}} [IsIntegral S] [IsIntegral X]
    (πS : S ⟶ Spec (.of k)) [IsProper πS]
    (mS : ℕ) (iS : S ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (mS + 1)) k))
    [IsClosedImmersion iS] (hiS : iS ≫ ProjSpace.π k mS = πS)
    (πX : X ⟶ Spec (.of k)) [IsProper πX]
    (mX : ℕ) (iX : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (mX + 1)) k))
    [IsClosedImmersion iX] (hiX : iX ≫ ProjSpace.π k mX = πX)
    (q : X ⟶ S) [IsProper q] [IsDominant q] (hqπ : q ≫ πS = πX)
    (η : S) (hη : IsGenericPoint η Set.univ) (hdim : topologicalKrullDim (q.fiber η) ≤ 1) :
    ∃ (N : Scheme.{u}) (qN : N ⟶ S) (U : Scheme.{u}) (u : U ⟶ N)
      (W : Scheme.{u}) (pW : W ⟶ U) (G : Scheme.{u})
      (fX : G ⟶ X) (fN : G ⟶ N) (tW : W ⟶ G),
      IsIntegral N ∧ (∀ x : N, IsIntegrallyClosed (N.presheaf.stalk x)) ∧
      IsProper qN ∧ Surjective qN ∧ topologicalKrullDim N = topologicalKrullDim S ∧
      IsIntegral U ∧ IsOpenImmersion u ∧ IsDominant u ∧ Smooth (u ≫ qN ≫ πS) ∧
      IsIntegral W ∧ Smooth pW ∧ IsProper pW ∧ Surjective pW ∧
      Smooth (pW ≫ u ≫ qN ≫ πS) ∧
      IsIntegral G ∧ (∀ x : G, IsIntegrallyClosed (G.presheaf.stalk x)) ∧
      IsProper fX ∧ Surjective fX ∧ IsProper fN ∧ Surjective fN ∧
      IsOpenImmersion tW ∧ IsDominant tW ∧ IsPullback tW pW fN u ∧
      (∀ ηN : N, IsGenericPoint ηN Set.univ →
        IsIntegral (fN.fiber ηN) ∧ Smooth (fN.fiberToSpecResidueField ηN) ∧
        IsProper (fN.fiberToSpecResidueField ηN) ∧ topologicalKrullDim (fN.fiber ηN) ≤ 1) ∧
      fX ≫ q = fN ≫ qN ∧ fX ≫ πX = fN ≫ qN ≫ πS ∧
      topologicalKrullDim G = topologicalKrullDim W ∧
      (∃ (dN : ℕ) (jN : N ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (dN + 1)) k)),
        IsClosedImmersion jN ∧ jN ≫ ProjSpace.π k dN = qN ≫ πS) ∧
      ∃ (dG : ℕ) (jG : G ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (dG + 1)) k)),
        IsClosedImmersion jG ∧ jG ≫ ProjSpace.π k dG = fX ≫ πX := by sorry
