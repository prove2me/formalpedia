-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_dense_affine_separating_function_field_parameters
-- name    : AlgebraicGeometry.exists_dense_affine_separating_function_field_parameters
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-23T16:59:24.959465+00:00
-- url     : https://prove2.me/theorems/a7647f93-654f-415c-b651-1f7a216d4105
-- title:
--   Separating function-field parameters on a dense affine chart
-- statement:
--   Let $K$ be a perfect field, let $X$ be an integral scheme locally of finite type over $K$, and let $K(X)$ be its function field with the $K$-algebra structure induced by the structure morphism. There is a finite subset $S\subset K(X)$ that is a transcendence basis and for which $K(X)/K(S)$ is a finite separable field extension.
--
--   There is a dense affine open $U\subset X$ on which every member of $S$ is represented by a regular function $a_s\in\Gamma(U,\mathcal O_U)$. These functions define a dominant $K$-morphism
--   $$f:U\longrightarrow\operatorname{Spec}K[T_s\mid s\in S],\qquad T_s\longmapsto a_s.$$
--   Its coordinate germs are exactly the chosen separating parameters. The finite set $S$ may be empty. This is the generic separating-parameter step used in constructing projections and curve fibrations for alteration arguments.
--
--   **Formalization Note.** The field is the stalk at the generic point of the actual scheme. The coefficient map is the map on sections induced by its structure morphism, and the displayed affine morphism is constructed from the polynomial evaluation homomorphism. Finiteness and separability are asserted for the function-field extension; compactification and smoothness of a projective fibration are further steps.
-- source:
--   Derived from finite separating transcendence bases over perfect fields and spreading finitely many rational functions to an affine open. Stacks Project, Algebra Sections 10.42 and 10.44, https://stacks.math.columbia.edu/tag/030I and https://stacks.math.columbia.edu/tag/05DT ; Mathlib lemma exists_isTranscendenceBasis_and_isSeparable_of_perfectField, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/FieldTheory/SeparablyGenerated.lean . This auxiliary scheme-level formulation supplies generic parameters for the projection step of de Jong, Smoothness, semi-stability and alterations (1996), Section 4.11, https://www.numdam.org/item/PMIHES_1996__83__51_0.pdf ; it does not state the alteration theorem.

import Mathlib
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u

theorem AlgebraicGeometry.exists_dense_affine_separating_function_field_parameters
    (K : Type u) [Field K] [PerfectField K]
    {X : Scheme.{u}} [IsIntegral X] (π : X ⟶ Spec (.of K)) [LocallyOfFiniteType π] :
    letI : Algebra K X.functionField :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫ π.appTop ≫
        X.presheaf.germ ⊤ (genericPoint X) trivial).hom.toAlgebra
    ∃ s : Finset X.functionField,
      IsTranscendenceBasis K ((↑) : s → X.functionField) ∧
      Module.Finite (IntermediateField.adjoin K (s : Set X.functionField)) X.functionField ∧
      Algebra.IsSeparable (IntermediateField.adjoin K (s : Set X.functionField)) X.functionField ∧
      ∃ (U : X.Opens) (hU : IsAffineOpen U), Dense (U : Set X) ∧
        ∃ hne : Nonempty U, ∃ a : s → Γ(X, U),
          (∀ t : s, @Scheme.germToFunctionField X _ U hne (a t) = t.val) ∧
          ∃ f : (U : Scheme) ⟶ Spec (.of (MvPolynomial s K)),
            f = hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
              (MvPolynomial.eval₂Hom
                ((Scheme.ΓSpecIso (.of K)).inv ≫ π.appLE ⊤ U (by simp)).hom a)) ∧
            IsDominant f ∧
            f ≫
            Spec.map (CommRingCat.ofHom (MvPolynomial.C : K →+* MvPolynomial s K)) = U.ι ≫ π := by sorry
