-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_normal_projective_model_of_finite_genericResidueField_extension
-- name    : AlgebraicGeometry.exists_normal_projective_model_of_finite_genericResidueField_extension
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-25T14:16:53.39276+00:00
-- url     : https://prove2.me/theorems/a2fa0ad5-6962-47c5-9e21-5fc176c6d9cb
-- title:
--   Normal projective base models realizing finite generic residue-field extensions
-- statement:
--   Let $k$ be a field and let $S$ be an integral proper $k$-scheme equipped with a projective embedding. Let $\eta$ be its generic point, put $F=\kappa(\eta)$, and let $E/F$ be a finite field extension with the compatible $k$-structure.
--
--   There are a normal finitely generated $k$-subalgebra
--   $$B\subset E,\qquad\operatorname{Frac}(B)=E,$$
--   a normal integral projective $k$-scheme $N$, a proper surjective $k$-morphism $q:N\to S$, and a dense open immersion $t:\operatorname{Spec}B\hookrightarrow N$ such that
--   $$\dim N=\dim S.$$
--   The chart has its specified $k$-structure. Its generic map realizes the given finite extension: the two composites
--   $$\operatorname{Spec}E\longrightarrow\operatorname{Spec}B
--    \xrightarrow{t}N\xrightarrow{q}S$$
--   and
--   $$\operatorname{Spec}E\longrightarrow\operatorname{Spec}F
--    \xrightarrow{\eta}S$$
--   are equal. Projectivity of $N$ is exhibited by a closed immersion into a finite-dimensional projective space, compatible with $q$ and the structure map of $S$.
--
--   The extension may be inseparable and the field $k$ may be imperfect. No normality of $S$ is assumed. The retained affine chart and fraction-field identification provide a global projective base for finite-field generic-curve constructions in alteration arguments. **Formalization Note.** The actual field $E$ is retained through the subalgebra $B$, its fraction field and the exact generic-spectrum equation. The morphism $q$ is proper and surjective; global finiteness of $q$, smoothness of $N$ and a semistable curve family are not asserted.
-- source:
--   Auxiliary finite-field base-model construction for the Philippon alteration branch. Finiteness of integral closure is the Proved https://prove2.me/theorems/9a74d075-f74a-5f5f-801f-29882692a8bb . The finite projective normalization and retained normal-open construction reuse the accepted source of https://prove2.me/theorems/7d122c2e-85fc-4c12-80b1-6a0ba09d0dca , with its unrelated separating-parameter theorem omitted. Image closure and projective products reuse https://prove2.me/theorems/8bdb0530-5db8-54fe-bd53-5026276eba53 and https://prove2.me/theorems/15fbefcf-89ea-5e7d-bf8e-af6412e75b66 . The field model retains the exact extension supplied to the generic-curve-fibration alteration frontier https://prove2.me/theorems/842dbd70-6333-40fa-86df-02394eb67249 . This is a normal projective base model, not a proof of semistable reduction or the remaining global alteration.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.exists_normal_projective_model_of_finite_genericResidueField_extension
    (k : Type u) [Field k] {S : Scheme.{u}} [IsIntegral S]
    (π : S ⟶ Spec (.of k)) [IsProper π]
    (m : ℕ) (i : S ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) k))
    [IsClosedImmersion i] (hi : i ≫ ProjSpace.π k m = π)
    (η : S) (hη : IsGenericPoint η Set.univ) :
    letI : Algebra k (S.residueField η) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ π.appTop ≫
        S.presheaf.germ ⊤ η trivial ≫ S.residue η).hom.toAlgebra
    ∀ (E : Type u) [Field E] [Algebra (S.residueField η) E] [Algebra k E]
      [IsScalarTower k (S.residueField η) E] [FiniteDimensional (S.residueField η) E],
    ∃ B : Subalgebra k E, Algebra.FiniteType k B ∧ IsIntegrallyClosed B ∧
      IsFractionRing B E ∧
      ∃ (N : Scheme.{u}) (q : N ⟶ S) (t : Spec (.of B) ⟶ N),
        IsIntegral N ∧ (∀ x : N, IsIntegrallyClosed (N.presheaf.stalk x)) ∧
        IsProper q ∧ Surjective q ∧ IsOpenImmersion t ∧ IsDominant t ∧
        topologicalKrullDim N = topologicalKrullDim S ∧
        t ≫ (q ≫ π) = Spec.map (CommRingCat.ofHom (algebraMap k B)) ∧
        Spec.map (CommRingCat.ofHom (algebraMap B E)) ≫ t ≫ q =
          Spec.map (CommRingCat.ofHom (algebraMap (S.residueField η) E)) ≫
            S.fromSpecResidueField η ∧
        ∃ (d : ℕ) (j : N ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k)),
          IsClosedImmersion j ∧ j ≫ ProjSpace.π k d = q ≫ π := by sorry
