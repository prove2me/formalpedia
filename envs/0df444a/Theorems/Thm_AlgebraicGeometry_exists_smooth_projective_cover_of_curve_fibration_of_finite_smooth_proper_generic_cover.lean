-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_smooth_projective_cover_of_curve_fibration_of_finite_smooth_proper_generic_cover
-- name    : AlgebraicGeometry.exists_smooth_projective_cover_of_curve_fibration_of_finite_smooth_proper_generic_cover
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-24T02:29:05.781656+00:00
-- url     : https://prove2.me/theorems/842dbd70-6333-40fa-86df-02394eb67249
-- title:
--   Alteration of a curve fibration supplied with a finite smooth proper generic cover
-- statement:
--   Let $K$ be algebraically closed. Let $G$ be an integral normal proper $K$-scheme with a specified projective embedding, and let
--   $$q:G\longrightarrow\mathbb P^r_K$$
--   be a proper surjective $K$-morphism, with $r>0$ and $\dim G=r+1$. Let $\eta$ be the generic point of this projective space, put $F=\kappa(\eta)$, and let $C=G\times_{\mathbb P^r_K}\operatorname{Spec}F$ be the actual generic fibre.
--
--   Suppose that a finite field extension $E/F$ and a smooth proper $E$-scheme $C_0$ are given, together with a proper surjective morphism
--   $$a:C_0\longrightarrow C$$
--   whose composite with $C\to\operatorname{Spec}F$ is the structure morphism of $C_0$ followed by $\operatorname{Spec}E\to\operatorname{Spec}F$.
--
--   Then there exist an integral smooth projective $K$-scheme $Y$ and a proper surjective $K$-morphism
--   $$f:Y\longrightarrow G.$$
--   Projectivity is exhibited by a closed immersion into projective space compatible with the structure morphism.
--
--   This is the remaining global alteration problem for a normal projective curve fibration after its generic curve has been supplied with a smooth proper cover over a finite extension. The conclusion does not specify that the generic fibre of $Y$ equals the given cover. Neither semistability nor a smooth total space extending that cover is a hypothesis. **Formalization Note.** No integrality, dimension bound or projective embedding of $C_0$ is assumed. Normality and a dimension-one condition on $C$, local-ring isomorphisms for its inclusion and a dense smooth source open have been removed from the earlier frontier formulation; the finite smooth proper generic-cover data are explicit inputs.
-- source:
--   Remaining alteration step in the Philippon mission after the finite-extension smooth proper curve cover. This is an auxiliary reduction of the Open theorem https://prove2.me/theorems/24700494-6f7d-4195-ba71-67cca0ce2ace , not a completed proof of de Jong alteration or semistable reduction. The finite-field cover supplied to this theorem is constructed from the Proved geometric-curve cover https://prove2.me/theorems/98944e77-2d0a-41a3-bad1-20bd6211e2e8 and the Proved relative descent https://prove2.me/theorems/8113d2fc-8253-4a8a-a56e-405a6f283432 .

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.exists_smooth_projective_cover_of_curve_fibration_of_finite_smooth_proper_generic_cover
    (K : Type u) [Field K] [IsAlgClosed K] {G : Scheme.{u}} [IsIntegral G]
    (π : G ⟶ Spec (.of K)) [IsProper π] (d : ℕ)
    (k : G ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) K))
    [IsClosedImmersion k] (hk : k ≫ ProjSpace.π K d = π)
    (r : ℕ) (q : G ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K))
    [IsProper q] [Surjective q] (hr : 0 < r)
    (hbase : q ≫ ProjSpace.π K r = π)
    (hnormal : ∀ g : G, IsIntegrallyClosed (G.presheaf.stalk g))
    (hdim : topologicalKrullDim G = ((r + 1 : ℕ) : WithBot ℕ∞))
    (η : Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K))
    (hη : IsGenericPoint η Set.univ)
    (E : Type u) [Field E] [Algebra ((Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K)).residueField η) E] [FiniteDimensional ((Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K)).residueField η) E]
    (C₀ : Scheme.{u}) (p : C₀ ⟶ Spec (.of E)) [Smooth p] [IsProper p]
    (a : C₀ ⟶ q.fiber η) [IsProper a] [Surjective a]
    (ha : a ≫ q.fiberToSpecResidueField η =
      p ≫ Spec.map (CommRingCat.ofHom (algebraMap ((Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K)).residueField η) E))) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ G),
      IsIntegral Y ∧ IsProper f ∧ Surjective f ∧ Smooth (f ≫ π) ∧
      ∃ (m : ℕ)
        (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K)),
        IsClosedImmersion j ∧ j ≫ ProjSpace.π K m = f ≫ π := by sorry
