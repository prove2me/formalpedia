-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_integral_projective_model_of_separating_parameters
-- name    : AlgebraicGeometry.exists_integral_projective_model_of_separating_parameters
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-23T17:37:09.079085+00:00
-- url     : https://prove2.me/theorems/0021f843-0328-443e-8ca5-a5857756c794
-- title:
--   A projective graph model carrying separating function-field parameters
-- statement:
--   Let $K$ be a perfect field and let $X$ be an integral proper $K$-scheme with a fixed projective embedding. There is a finite separating transcendence basis $S\subset K(X)$ with $r=|S|=\dim X$, a dense affine open $U\subset X$, and regular functions on $U$ representing the members of $S$. Their polynomial evaluation defines a dominant $K$-morphism $f:U\to\mathbb A^r_K$.
--
--   There are an integral projective $K$-scheme $G$, proper morphisms $p:G\to X$ and $q:G\to\mathbb P^r_K$, a dense open immersion $t:U\hookrightarrow G$, and an open immersion $e:\mathbb A^r_K\hookrightarrow\mathbb P^r_K$ over $K$ such that
--   $$p\circ t=\iota_U,\qquad q\circ t=e\circ f,\qquad\dim G=\dim X.$$
--   The morphism $p$ is surjective, and its map on local rings is an isomorphism at every point $t(u)$. The structure maps of $p$ and $q$ agree. Projectivity of $G$ is exhibited by a closed immersion into an actual projective space over $K$. The field extension $K(X)/K(S)$ is finite separable, with the base-field algebra structure induced by the original morphism.
--
--   This is an auxiliary graph-model construction for extending generic separating parameters to a projective projection. **Formalization Note.** The affine map is specified by the actual polynomial evaluation homomorphism and the parameter germs. Finiteness is recorded for the function-field extension; the global projective map $q$ is asserted to be proper. Normalization and the construction of a suitable curve fibration remain subsequent geometric steps.
-- source:
--   Auxiliary consequence of separating transcendence bases and the projective closure of a graph. Stacks Project, Lemma 29.7.7, https://stacks.math.columbia.edu/tag/01RG ; scheme-theoretic images, https://stacks.math.columbia.edu/tag/01R5 ; varieties and rational maps, https://stacks.math.columbia.edu/tag/0BXM ; projective morphisms and Segre embeddings, https://stacks.math.columbia.edu/tag/01W7 . Uses the proved separating-parameter theorem https://prove2.me/theorems/a7647f93-654f-415c-b651-1f7a216d4105 . This is supporting infrastructure for the projection step in A. J. de Jong, Smoothness, semi-stability and alterations (1996), Section 4.11, https://www.numdam.org/item/PMIHES_1996__83__51_0.pdf ; it does not assert that full curve-fibration or alteration step.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.exists_integral_projective_model_of_separating_parameters
    (K : Type u) [Field K] [PerfectField K] {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of K)) [IsProper π] (n : ℕ)
    (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K))
    [IsClosedImmersion i] (hi : i ≫ ProjSpace.π K n = π) :
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
              IsIntegral G ∧ topologicalKrullDim G = topologicalKrullDim X ∧
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
