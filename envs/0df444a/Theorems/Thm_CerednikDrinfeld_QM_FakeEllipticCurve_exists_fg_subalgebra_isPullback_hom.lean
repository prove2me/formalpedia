-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_isPullback_hom
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_fg_subalgebra_isPullback_hom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/a1ab5e97-0bcd-5727-bf6d-c5cbaae4de7b
-- title:
--   Descent of a fake elliptic curve to a finitely generated subring
-- statement:
--   Fix rationals $a,b$ and a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ which is a maximal order, in the sense that $\Lambda$ is an order and every order containing it equals it; fix a natural number $N$, a commutative ring $R$ (in the bottom universe) and a fake elliptic curve $E$ over $R$ with $\Lambda$-action and level datum $N$, that is: a scheme $E.A$ with a structure morphism $E.f : E.A \to \operatorname{Spec} R$ which is smooth, proper and has connected fibres, a commutative relative group law $E.L$ on the functor of sections of $E.f$, fibres of topological Krull dimension $2$, an additive and multiplicative action $E.\mathrm{act}$ of $\Lambda$ by endomorphisms of $E.A$ over $\operatorname{Spec} R$ respecting the group law and satisfying the trace condition on tangent spaces, together with the level-$N$ data. The assertion is that there exist a subalgebra $T \subseteq R$ over $\mathbb{Z}$ which is finitely generated as a $\mathbb{Z}$-algebra, a fake elliptic curve $ET$ over $T$ for the same $\Lambda$ and $N$, and a morphism $g : E.A \to ET.A$ such that the square formed by $g$, $E.f$, $ET.f$ and $\operatorname{Spec}$ of the inclusion $T \to R$ is cartesian, and moreover: for every scheme $X$, every $t' : X \to \operatorname{Spec} R$ and all sections $P,Q$ of $E.f$ over $t'$, composing the product $E.L.\mathrm{mul}\,t'\,P\,Q$ with $g$ gives the product in $ET.L$ over $t'$ followed by $\operatorname{Spec}$ of the inclusion of the images of $P$ and $Q$ under $g$; and $E.\mathrm{act}\,x$ followed by $g$ equals $g$ followed by $ET.\mathrm{act}\,x$ for every $x \in \Lambda$. Thus the conclusion records the first two clauses of the relation `FakeEllipticCurve.IsPullback` for the inclusion $T \to R$; the clause about compatibility of level structures is not asserted.
--
--   This is the spreading-out (descent to a base of finite type) step for the moduli problem of fake elliptic curves: any such object over an arbitrary commutative ring comes, together with its group law and quaternionic action, by base change from one over a finitely generated subring. It is used in the construction of isogeny pairs over fine moduli data and in the companion statement that additionally produces a two-torsion kernel datum and an isomorphism of pullbacks.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_isPullback_hom.lean

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_fg_subalgebra_isPullback_hom
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (N : ℕ) (R : Type) [CommRing R] (E : FakeEllipticCurve Λ N R) :
    ∃ (T : Subalgebra ℤ R) (_ : T.FG) (ET : FakeEllipticCurve Λ N ↥T) (g : E.A ⟶ ET.A)
      (hg : CategoryTheory.IsPullback g E.f ET.f (Spec.map (CommRingCat.ofHom T.val.toRingHom))),
      (∀ {X : Scheme.{0}} (t' : X ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t' E.f),
        (E.L.mul t' P Q).1 ≫ g =
          (ET.L.mul (t' ≫ Spec.map (CommRingCat.ofHom T.val.toRingHom))
            ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1) ∧
      (∀ x : ↥Λ, E.act x ≫ g = g ≫ ET.act x) := by sorry
