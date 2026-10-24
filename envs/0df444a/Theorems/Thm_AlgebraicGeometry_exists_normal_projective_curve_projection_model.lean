-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_normal_projective_curve_projection_model
-- name    : AlgebraicGeometry.exists_normal_projective_curve_projection_model
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-23T19:08:50.236497+00:00
-- url     : https://prove2.me/theorems/443127a4-5bf9-4291-bb4e-9de03aa84d66
-- title:
--   Normal projective projection model with one remaining transcendental parameter
-- statement:
--   Let $K$ be a perfect field. Let $X$ be an integral normal proper $K$-scheme, equipped with a projective embedding, and assume $\dim X>1$. There is a finite separating transcendence basis $S\subset K(X)$, an element $x\in S$, and the remaining parameter set $T=S\setminus\{x\}$. Put $r=|T|$. Then
--   $$r>0,\qquad \dim X=r+1,\qquad \operatorname{trdeg}_{K(T)}K(X)=1.$$
--   The element $x$ is a transcendence basis of $K(X)$ over $K(T)$, and $K(X)/K(S)$ is finite separable.
--
--   There are an integral normal projective $K$-scheme $G$, proper surjective morphisms $p:G\to X$ and $q:G\to\mathbb P^r_K$, a common dense affine parameter chart $U\subset X$, and a dense open immersion $t:U\hookrightarrow G$. There are regular functions on $U$ representing all members of $S$; their polynomial evaluation defines a dominant map $f:U\to\mathbb A^{|S|}_K$. If $\mathrm{pr}:\mathbb A^{|S|}_K\to\mathbb A^r_K$ forgets the coordinate $x$ and $e:\mathbb A^r_K\hookrightarrow\mathbb P^r_K$ is an open immersion over $K$, then
--   $$p\circ t=\iota_U,\qquad q\circ t=e\circ\mathrm{pr}\circ f,\qquad\dim G=\dim X.$$
--   The maps $p$ and $q$ have the same structure morphism over $K$. The map of local rings induced by $p$ is an isomorphism at every point $t(u)$. Projectivity of $G$ is witnessed by a closed immersion into an actual projective space.
--
--   This gives a proper normal projection model with one remaining function-field parameter, as preparation for a curve-fibration argument. **Formalization Note.** The actual function field, its base-field algebra structure, coordinate germs, polynomial evaluation and variable-renaming map are recorded. The field-theoretic relative transcendence degree is one; the statement does not assert equidimensionality or smoothness of all geometric fibres, flatness, or semistability.
-- source:
--   Auxiliary projection construction, weaker than the fibrewise assertions in A. J. de Jong, Smoothness, semi-stability and alterations (1996), Lemma 4.11 and Section 4.12, pp.67-69, https://www.numdam.org/item/PMIHES_1996__83__51_0.pdf . Uses a separating transcendence basis, forgets one coordinate, takes the integral projective graph, and normalizes while retaining its normal chart. Stacks Project, transcendence bases and towers, Lemma 9.26.5, https://stacks.math.columbia.edu/tag/030H ; graph image factorization, Lemma 29.7.7, https://stacks.math.columbia.edu/tag/01RG ; normalization, Lemmas 33.27.1-33.27.2, https://stacks.math.columbia.edu/tag/0BXQ ; normality of normalization and isomorphism over normal opens, Section 29.55, https://stacks.math.columbia.edu/tag/035E . The finite separating-parameter input is https://prove2.me/theorems/a7647f93-654f-415c-b651-1f7a216d4105 . This statement does not claim the full Lemma 4.11 or a regular alteration.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.exists_normal_projective_curve_projection_model
    (K : Type u) [Field K] [PerfectField K] {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of K)) [IsProper π] (n : ℕ)
    (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K))
    [IsClosedImmersion i] (hi : i ≫ ProjSpace.π K n = π)
    (hnormalX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hdim : 1 < topologicalKrullDim X) :
    letI : Algebra K X.functionField :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫ π.appTop ≫
        X.presheaf.germ ⊤ (genericPoint X) trivial).hom.toAlgebra
    ∃ S : Finset X.functionField,
      IsTranscendenceBasis K ((↑) : S → X.functionField) ∧
      Module.Finite (IntermediateField.adjoin K (S : Set X.functionField)) X.functionField ∧
      Algebra.IsSeparable (IntermediateField.adjoin K (S : Set X.functionField)) X.functionField ∧
      ∃ (x : S) (T : Finset X.functionField) (j : T ↪ S),
        (T : Set X.functionField) = (S : Set X.functionField) \ {x.val} ∧
        (∀ z : T, (j z).val = z.val) ∧
        0 < Fintype.card T ∧
        topologicalKrullDim X = ((Fintype.card T + 1 : ℕ) : WithBot ℕ∞) ∧
        IsTranscendenceBasis (IntermediateField.adjoin K (T : Set X.functionField))
          (fun _ : Unit => x.val) ∧
        Algebra.trdeg (IntermediateField.adjoin K (T : Set X.functionField)) X.functionField = 1 ∧
        ∃ (U : X.Opens) (hU : IsAffineOpen U), Dense (U : Set X) ∧
          ∃ hne : Nonempty U, ∃ a : S → Γ(X, U),
            (∀ z : S, @Scheme.germToFunctionField X _ U hne (a z) = z.val) ∧
            ∃ f : (U : Scheme) ⟶ Spec (.of (MvPolynomial S K)),
              f = hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
                (MvPolynomial.eval₂Hom
                  ((Scheme.ΓSpecIso (.of K)).inv ≫ π.appLE ⊤ U (by simp)).hom a)) ∧
              IsDominant f ∧
              f ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.C : K →+* MvPolynomial S K)) = U.ι ≫ π ∧
              ∃ (G : Scheme.{u}) (p : G ⟶ X)
                (q : G ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (Fintype.card T + 1)) K))
                (t : (U : Scheme) ⟶ G)
                (e : Spec (.of (MvPolynomial T K)) ⟶
                  Proj (MvPolynomial.homogeneousSubmodule (Fin (Fintype.card T + 1)) K)),
                IsIntegral G ∧ (∀ g : G, IsIntegrallyClosed (G.presheaf.stalk g)) ∧
                topologicalKrullDim G = topologicalKrullDim X ∧
                IsProper p ∧ Surjective p ∧ IsProper q ∧ Surjective q ∧
                IsOpenImmersion t ∧ IsDominant t ∧
                (∀ u : (U : Scheme), IsIso (p.stalkMap (t u))) ∧
                IsOpenImmersion e ∧
                e ≫ ProjSpace.π K (Fintype.card T) =
                  Spec.map (CommRingCat.ofHom (MvPolynomial.C : K →+* MvPolynomial T K)) ∧
                t ≫ p = U.ι ∧
                t ≫ q = f ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.rename (R := K) j)) ≫ e ∧
                p ≫ π = q ≫ ProjSpace.π K (Fintype.card T) ∧
                ∃ (d : ℕ)
                  (k : G ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) K)),
                  IsClosedImmersion k ∧ k ≫ ProjSpace.π K d = p ≫ π := by sorry
