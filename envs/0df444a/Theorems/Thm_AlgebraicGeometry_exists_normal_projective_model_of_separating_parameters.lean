-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_normal_projective_model_of_separating_parameters
-- name    : AlgebraicGeometry.exists_normal_projective_model_of_separating_parameters
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-23T18:45:49.882418+00:00
-- url     : https://prove2.me/theorems/7d122c2e-85fc-4c12-80b1-6a0ba09d0dca
-- title:
--   A normal projective model retaining separating parameters and their affine chart
-- statement:
--   Let $K$ be a perfect field and let $X$ be an integral proper $K$-scheme equipped with a projective embedding. Assume that every local ring of $X$ is integrally closed. There is a finite separating transcendence basis $S\subset K(X)$ with $r=|S|=\dim X$, a dense affine open $U\subset X$, and regular functions representing all the members of $S$. Their polynomial evaluation gives a dominant $K$-morphism $f:U\to\mathbb A^r_K$.
--
--   There are an integral normal projective $K$-scheme $G$, proper morphisms $p:G\to X$ and $q:G\to\mathbb P^r_K$, a dense open immersion $t:U\hookrightarrow G$, and an open immersion $e:\mathbb A^r_K\hookrightarrow\mathbb P^r_K$ over $K$ such that
--   $$p\circ t=\iota_U,\qquad q\circ t=e\circ f,\qquad \dim G=\dim X.$$
--   The morphism $p$ is surjective and induces isomorphisms of local rings at all points $t(u)$. Both projections have the same structure morphism over $K$. Projectivity is witnessed by a closed immersion of $G$ into an actual projective space, and normality by integral closedness of every local ring. The extension $K(X)/K(S)$ is finite separable.
--
--   This constructs a normal projective model carrying the original separating parameters, for use in alteration arguments. **Formalization Note.** The parameter germs, the polynomial evaluation homomorphism, and the base-field algebra structure are recorded explicitly. The projective map $q$ is proper; no global finiteness or smoothness of $q$ is asserted.
-- source:
--   Auxiliary consequence of normalization and projective graph closure. Stacks Project, Section 33.27, Lemmas 33.27.1 and 33.27.2 (normalization is finite and projective), https://stacks.math.columbia.edu/tag/0BXQ ; Section 29.55, Lemmas 29.55.4 and 29.55.9 (normalization and normal local rings), https://stacks.math.columbia.edu/tag/035E ; projectivity and composition, https://stacks.math.columbia.edu/tag/01W7 . Starts from the proved separating projective graph theorem https://prove2.me/theorems/0021f843-0328-443e-8ca5-a5857756c794 . Supporting step toward A. J. de Jong, Smoothness, semi-stability and alterations (1996), Sections 4.10 and 4.11, https://www.numdam.org/item/PMIHES_1996__83__51_0.pdf ; the statement does not include the later curve-fibration or alteration construction.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.exists_normal_projective_model_of_separating_parameters
    (K : Type u) [Field K] [PerfectField K] {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of K)) [IsProper π] (n : ℕ)
    (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K))
    [IsClosedImmersion i] (hi : i ≫ ProjSpace.π K n = π)
    (hnormalX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) :
    letI : Algebra K X.functionField :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫ π.appTop ≫
        X.presheaf.germ ⊤ (genericPoint X) trivial).hom.toAlgebra
    ∃ S : Finset X.functionField,
      IsTranscendenceBasis K ((↑) : S → X.functionField) ∧
      Module.Finite (IntermediateField.adjoin K (S : Set X.functionField)) X.functionField ∧
      Algebra.IsSeparable (IntermediateField.adjoin K (S : Set X.functionField)) X.functionField ∧
      topologicalKrullDim X = (Fintype.card S : WithBot ℕ∞) ∧
      ∃ (U : X.Opens) (hU : IsAffineOpen U), Dense (U : Set X) ∧
        ∃ hne : Nonempty U, ∃ a : S → Γ(X, U),
          (∀ x : S, @Scheme.germToFunctionField X _ U hne (a x) = x.val) ∧
          ∃ f : (U : Scheme) ⟶ Spec (.of (MvPolynomial S K)),
            f = hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
              (MvPolynomial.eval₂Hom
                ((Scheme.ΓSpecIso (.of K)).inv ≫ π.appLE ⊤ U (by simp)).hom a)) ∧
            IsDominant f ∧
            f ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.C : K →+* MvPolynomial S K)) = U.ι ≫ π ∧
            ∃ (G : Scheme.{u}) (p : G ⟶ X)
              (q : G ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (Fintype.card S + 1)) K))
              (t : (U : Scheme) ⟶ G)
              (e : Spec (.of (MvPolynomial S K)) ⟶
                Proj (MvPolynomial.homogeneousSubmodule (Fin (Fintype.card S + 1)) K)),
              IsIntegral G ∧ (∀ g : G, IsIntegrallyClosed (G.presheaf.stalk g)) ∧
              topologicalKrullDim G = topologicalKrullDim X ∧
              IsProper p ∧ Surjective p ∧ IsProper q ∧
              IsOpenImmersion t ∧ IsDominant t ∧
              (∀ u : (U : Scheme), IsIso (p.stalkMap (t u))) ∧
              IsOpenImmersion e ∧
              e ≫ ProjSpace.π K (Fintype.card S) =
                Spec.map (CommRingCat.ofHom (MvPolynomial.C : K →+* MvPolynomial S K)) ∧
              t ≫ p = U.ι ∧ t ≫ q = f ≫ e ∧
              p ≫ π = q ≫ ProjSpace.π K (Fintype.card S) ∧
              ∃ (d : ℕ)
                (k : G ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) K)),
                IsClosedImmersion k ∧ k ≫ ProjSpace.π K d = p ≫ π := by sorry
