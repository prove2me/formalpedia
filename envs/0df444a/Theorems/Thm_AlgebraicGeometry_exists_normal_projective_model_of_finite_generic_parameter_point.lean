-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_normal_projective_model_of_finite_generic_parameter_point
-- name    : AlgebraicGeometry.exists_normal_projective_model_of_finite_generic_parameter_point
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-26T16:49:33.411347+00:00
-- url     : https://prove2.me/theorems/9afbffc7-8dee-40bf-9031-f73fed45feef
-- title:
--   A normal projective base model realizing a finite generic parameter point
-- statement:
--   Let $k$ be a field, $S$ an integral proper projective $k$-scheme, and $M$ any proper projective $k$-scheme, each with a specified closed projective embedding. Let $\eta$ be the actual generic point of $S$. Give $\kappa(\eta)$ its structure as a $k$-algebra through $S$, and let $E/\kappa(\eta)$ be a finite extension with the compatible $k$-algebra structure. Suppose a specified point
--   $$m:\operatorname{Spec}E\longrightarrow M$$
--   is a $k$-morphism.
--
--   There is a normal integral projective $k$-scheme $T$, a proper surjection $q:T\to S$, a proper $k$-morphism $b:T\to M$, and a dominant field-valued preimmersion $t:\operatorname{Spec}E\to T$ such that
--   $$q\circ t=(\operatorname{Spec}E\to\operatorname{Spec}\kappa(\eta)\to S),\qquad b\circ t=m.$$
--   The two morphisms have the same $k$-structure, and
--   $$\dim T=\dim S.$$
--   A specified closed projective embedding of this same $T$, with structure map exactly $q$ followed by that of $S$, is retained. No dominance or surjectivity onto $M$ is required.
--
--   The theorem extends a supplied generic point of a projective parameter space to a normal projective model while retaining its actual field and value. It supplies the parameter-map portion of the curve-family extension argument; existence of a stable-curve parameter space and its classifying point, and regularization of the resulting family, are separate assertions.
-- source:
--   Auxiliary parameter-model consequence of A. J. de Jong, Smoothness, semi-stability and alterations, Publications Mathématiques de l’IHÉS 83 (1996), Section 4.17, pp. 71-72, https://www.numdam.org/item/PMIHES_1996__83__51_0.pdf . Section 4.17 extends a lifted moduli map by taking its projective graph closure. This statement isolates that construction for any supplied projective parameter space and finite generic-field point, with finite normalization retaining the original normal open. It reuses the accepted actual finite-field base model https://prove2.me/theorems/a2fa0ad5-6962-47c5-9e21-5fc176c6d9cb and principal morphism spreading https://prove2.me/theorems/fea98ca8-9768-4de4-afef-adb65e69e6eb . It is an auxiliary derived statement, not a verbatim theorem of de Jong, and does not assert existence of stable moduli or a global smooth alteration.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.exists_normal_projective_model_of_finite_generic_parameter_point
    (k : Type u) [Field k] {S M : Scheme.{u}} [IsIntegral S]
    (πS : S ⟶ Spec (.of k)) [IsProper πS]
    (dS : ℕ) (iS : S ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (dS + 1)) k))
    [IsClosedImmersion iS] (hiS : iS ≫ ProjSpace.π k dS = πS)
    (πM : M ⟶ Spec (.of k)) [IsProper πM]
    (dM : ℕ) (iM : M ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (dM + 1)) k))
    [IsClosedImmersion iM] (hiM : iM ≫ ProjSpace.π k dM = πM)
    (η : S) (hη : IsGenericPoint η Set.univ) :
    letI : Algebra k (S.residueField η) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ πS.appTop ≫
        S.presheaf.germ ⊤ η trivial ≫ S.residue η).hom.toAlgebra
    ∀ (E : Type u) [Field E] [Algebra (S.residueField η) E] [Algebra k E]
      [IsScalarTower k (S.residueField η) E] [FiniteDimensional (S.residueField η) E]
      (m : Spec (.of E) ⟶ M)
      (hm : m ≫ πM = Spec.map (CommRingCat.ofHom (algebraMap k E))),
    ∃ (T : Scheme.{u}) (q : T ⟶ S) (b : T ⟶ M) (t : Spec (.of E) ⟶ T),
      IsIntegral T ∧ (∀ x : T, IsIntegrallyClosed (T.presheaf.stalk x)) ∧
      IsProper q ∧ Surjective q ∧ IsProper b ∧ IsDominant t ∧ IsPreimmersion t ∧
      t ≫ q = Spec.map (CommRingCat.ofHom (algebraMap (S.residueField η) E)) ≫
        S.fromSpecResidueField η ∧
      t ≫ b = m ∧ q ≫ πS = b ≫ πM ∧
      topologicalKrullDim T = topologicalKrullDim S ∧
      ∃ (d : ℕ) (i : T ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k)),
        IsClosedImmersion i ∧ i ≫ ProjSpace.π k d = q ≫ πS := by sorry
