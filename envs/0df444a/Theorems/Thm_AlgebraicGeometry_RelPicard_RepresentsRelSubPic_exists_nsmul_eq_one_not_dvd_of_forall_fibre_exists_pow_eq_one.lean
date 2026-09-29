-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_nsmul_eq_one_not_dvd_of_forall_fibre_exists_pow_eq_one
-- name    : AlgebraicGeometry.RelPicard.RepresentsRelSubPic.exists_nsmul_eq_one_not_dvd_of_forall_fibre_exists_pow_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/7f1e37e1-b5ba-599a-b9c1-5fd4d04ed9e3
-- title:
--   Prime-to-p torsion for K-points of the Pic⁰ representing scheme
-- statement:
--   Let $c \colon C \to \operatorname{Spec}\mathbb{Z}$ be a morphism of schemes, let $\varepsilon$ be a section of $c$ (a morphism $\operatorname{Spec}\mathbb{Z} \to C$ whose composite with $c$ is the identity), and let $D$ consist of a scheme together with a structure morphism `D.toBase` to $\operatorname{Spec}\mathbb{Z}$ and a zero section of it. Let $hD$ witness that `D.toBase` represents the subfunctor of $\varepsilon$-rigidified line bundles on $C$ cut out by the condition that, for every algebraically closed field $k$ and every $k$-point $s$ of the base, the restriction of the bundle to the fibre of $c$ at $s$ satisfies `IsAlgEquivZero`: that is, a rigidified bundle (the Poincaré bundle) on `D.toBase` satisfying this condition, the universal property that every rigidified bundle satisfying it over a base $t$ is the pullback of the Poincaré bundle along a unique $t$-morphism to `D.toBase`, and triviality of the pullback along the zero section. Let $p$ be a natural number. Assume that for every algebraically closed field $K$ of characteristic $p$ in which every unit has finite order, every class $\xi$ in the cut group of rigidified bundles over $\operatorname{Spec} K$ — the group whose multiplication is tensor product of rigidified bundles, with the trivial class as unit — satisfies $\xi^{m} = 1$ for some $m > 0$ with $p \nmid m$. Then for every such $K$ and every section $x$ of `D.toBase` over $\operatorname{Spec} K \to \operatorname{Spec}\mathbb{Z}$ there is an $m > 0$ with $p \nmid m$ such that the $m$-fold iterate of $x$ under the relative group law on `D.toBase` induced by representability equals the identity section.
--
--   This transports a fibrewise prime-to-$p$ torsion statement for classes in the rigidified relative Picard functor to the points of the scheme representing it, in the situation of the relative $\mathrm{Pic}^0$ of a curve over $\mathbb{Z}$. It is used in the analysis of the characteristic-$p$ points of the Jacobian model attached to a modular curve, via [`ModularCurve.DRModelPackage.exists_schemeNsmul_eq_one_residueField_point`](thm.html#ModularCurve.DRModelPackage.exists_schemeNsmul_eq_one_residueField_point).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_nsmul_eq_one_not_dvd_of_forall_fibre_exists_pow_eq_one.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
open scoped CategoryTheory.MonObj

theorem AlgebraicGeometry.RelPicard.RepresentsRelSubPic.exists_nsmul_eq_one_not_dvd_of_forall_fibre_exists_pow_eq_one
    {C : Scheme.{0}} (c : C ⟶ Spec (CommRingCat.of ℤ))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℤ))) c)
    (D : RelativePic0Designation ℤ c)
    (hD : RepresentsRelSubPic c ε (algEquivZeroGroupCut c ε).toSubPicCondition D) (p : ℕ)

    (hfin : ∀ (K : Type) [Field K] [CharP K p] [IsAlgClosed K], (∀ u : Kˣ, IsOfFinOrder u) →
      letI := (algEquivZeroGroupCut c ε).commGroupObj (Opposite.op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℤ K)))))
      ∀ ξ : (relSubPicPresheaf c ε (algEquivZeroGroupCut c ε).toSubPicCondition).obj
          (Opposite.op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℤ K))))),
        ∃ m : ℕ, 0 < m ∧ ¬ p ∣ m ∧ ξ ^ m = 1)
    (K : Type) [Field K] [CharP K p] [IsAlgClosed K] (hK : ∀ u : Kˣ, IsOfFinOrder u)
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ K))) D.toBase) :
    ∃ m : ℕ, 0 < m ∧ ¬ p ∣ m ∧ hD.relativeGroupLaw.nsmul _ m x = hD.relativeGroupLaw.one _ := by sorry
