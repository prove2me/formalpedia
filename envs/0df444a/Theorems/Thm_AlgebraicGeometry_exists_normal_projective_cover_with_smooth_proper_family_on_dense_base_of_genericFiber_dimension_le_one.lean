-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_normal_projective_cover_with_smooth_proper_family_on_dense_base_of_genericFiber_dimension_le_one
-- name    : AlgebraicGeometry.exists_normal_projective_cover_with_smooth_proper_family_on_dense_base_of_genericFiber_dimension_le_one
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-25T23:18:58.617976+00:00
-- url     : https://prove2.me/theorems/35dae9aa-ba03-4a0c-aea4-045bcc94f746
-- title:
--   A normal projective cover retaining a smooth proper family over an altered base
-- statement:
--   Let $k$ be a perfect field and let $S,X$ be integral proper projective $k$-schemes with specified projective embeddings. Let $q:X\to S$ be a proper dominant $k$-morphism. Fix the actual generic point $\eta$ of $S$, and suppose
--   $$\dim X_\eta\leq1.$$
--
--   There are a normal integral projective $k$-scheme $N$, a proper surjection $q_N:N\to S$ with $\dim N=\dim S$, and a dense integral open $u:U\hookrightarrow N$ whose structure morphism to $k$ is smooth. There are also an integral scheme $W$, a smooth proper surjection $p_W:W\to U$, and a normal integral projective $k$-scheme $G$ with proper surjections
--   $$f_X:G\to X,\qquad f_N:G\to N.$$
--   The diagram over the original base commutes exactly:
--   $$q\circ f_X=q_N\circ f_N.$$
--   A specified dense open immersion $t_W:W\hookrightarrow G$ identifies the whole family with the actual restriction of $G$:
--   $$W\simeq G\times_N U.$$
--   The total space $W$ is smooth over $k$. Both maps from $G$ have the same $k$-structure, and $\dim G=\dim W$. The projective embeddings of both $N$ and this same $G$ are retained with their structure-map equations.
--
--   The construction uses the finite-generic-field covering data and its normal projective completion. It holds in arbitrary universes and characteristic over perfect fields. The conclusion records the smooth proper family on the dense base open and a normal global model. It does not assert a dimension bound for every fibre of that family, or smoothness of $G$ along the remaining boundary; fibre-dimension control, semistable extension and global smooth alteration remain further steps.
-- source:
--   Application to the Philippon global curve-fibration alteration frontier https://prove2.me/theorems/842dbd70-6333-40fa-86df-02394eb67249 . Combines the Proved actual finite-base covering-family theorem https://prove2.me/theorems/ae594a3b-8d61-41b8-8e72-b6a40e8b9e2f and the Proved normal projective family-completion theorem https://prove2.me/theorems/77bad564-392b-4202-9bf6-e267f19ec58c . A dense absolute smooth base open is obtained over the perfect field; an absolute projective immersion is constructed from the relative projective model; equality of the global maps over the original base extends from their exact equality on the retained dense open by reducedness and separatedness. This is a global normal model, not the final global smooth alteration.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.exists_normal_projective_cover_with_smooth_proper_family_on_dense_base_of_genericFiber_dimension_le_one
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
      fX ≫ q = fN ≫ qN ∧ fX ≫ πX = fN ≫ qN ≫ πS ∧
      topologicalKrullDim G = topologicalKrullDim W ∧
      (∃ (dN : ℕ) (jN : N ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (dN + 1)) k)),
        IsClosedImmersion jN ∧ jN ≫ ProjSpace.π k dN = qN ≫ πS) ∧
      ∃ (dG : ℕ) (jG : G ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (dG + 1)) k)),
        IsClosedImmersion jG ∧ jG ≫ ProjSpace.π k dG = fX ≫ πX := by sorry
