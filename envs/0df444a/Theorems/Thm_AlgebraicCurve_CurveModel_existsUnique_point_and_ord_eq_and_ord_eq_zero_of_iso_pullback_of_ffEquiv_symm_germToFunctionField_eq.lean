-- Prove2me | Theorems.Thm_AlgebraicCurve_CurveModel_existsUnique_point_and_ord_eq_and_ord_eq_zero_of_iso_pullback_of_ffEquiv_symm_germToFunctionField_eq
-- name    : AlgebraicCurve.CurveModel.existsUnique_point_and_ord_eq_and_ord_eq_zero_of_iso_pullback_of_ffEquiv_symm_germToFunctionField_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/6fa49256-76bc-5fc9-83f4-be3912330887
-- title:
--   Points and orders under an algebraically closed constant field extension
-- statement:
--   Let $\varphi\colon\kappa\to k$ be a ring homomorphism between algebraically closed fields, let $F_0$ be a field extension of $\kappa$ and $F$ a field extension of $k$, and let $M_0$ and $M$ be curve models of $F_0/\kappa$ and of $F/k$: that is, integral schemes $M_0.C$, $M.C$ with proper, smooth of relative dimension one structure morphisms to $\operatorname{Spec}\kappa$, resp. $\operatorname{Spec} k$, ring isomorphisms of $F_0$, resp. $F$, with the function fields compatible with the constant fields, and bijections from the closed points onto the places (valuation subrings containing the constant field, proper, with principal ideals) realising each stalk as the place's valuation ring, all finite sets of points lying in an affine open. Assume given an isomorphism $e\colon M.C\cong M_0.C\times_{\operatorname{Spec}\kappa}\operatorname{Spec} k$ whose composite with the second projection is $M.toBase$, and a ring homomorphism $\psi\colon F_0\to F$ such that, writing $\mathrm{pr}$ for $e.hom$ followed by the first projection, for every open $U\subseteq M_0.C$ with $U$ and $\mathrm{pr}^{-1}U$ non-empty and every $s\in\Gamma(M_0.C,U)$, the germ at the generic point of $\mathrm{pr}^{*}s$, read in $F$ via $M.ffEquiv^{-1}$, equals $\psi$ of the germ of $s$ read in $F_0$ via $M_0.ffEquiv^{-1}$. Then three assertions hold. First, every section $y_0$ of $M_0.toBase$ (a $\kappa$-point) admits a unique section $y$ of $M.toBase$ with $y\circ$-composite $y.1 \ggg \mathrm{pr}$ equal to $\operatorname{Spec}\varphi$ followed by $y_0$. Secondly, for any such compatible pair the valuation subring of the place associated with $y$ under `pointEquivPlace` pulls back along $\psi$ to the valuation subring of the place associated with $y_0$, and $\operatorname{ord}$ (minus the logarithm of the adic valuation) satisfies $\operatorname{ord}_{y}(\psi f)=\operatorname{ord}_{y_0}(f)$ for all $f\in F_0$. Thirdly, if a place $Q$ of $F/k$ is distinct from the place of $y$ for every compatible pair $(y_0,y)$, then $\operatorname{ord}_Q(\psi f)=0$ for all non-zero $f\in F_0$.
--
--   This is the behaviour of places and of orders of rational functions under an extension of algebraically closed constant fields: rational points lift uniquely and unramified, and functions coming from the smaller field are units at all places not lying over a base-changed point, so that the divisor of $\psi f$ is the base change of the divisor of $f$. It is used in the construction of curve models over $\mathbb{C}$ for quaternionic Shimura curves and in the comparison of integral models of modular curves with their function-field charts.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_CurveModel_existsUnique_point_and_ord_eq_and_ord_eq_zero_of_iso_pullback_of_ffEquiv_symm_germToFunctionField_eq.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

universe u v w

theorem AlgebraicCurve.CurveModel.existsUnique_point_and_ord_eq_and_ord_eq_zero_of_iso_pullback_of_ffEquiv_symm_germToFunctionField_eq
    {κ : Type u} [Field κ] [IsAlgClosed κ] {k : Type u} [Field k] [IsAlgClosed k] (φ : κ →+* k)
    {F₀ : Type v} [Field F₀] [Algebra κ F₀] {F : Type w} [Field F] [Algebra k F]
    (M₀ : CurveModel κ F₀) (M : CurveModel k F)
    (e : M.C ≅ pullback M₀.toBase (Spec.map (CommRingCat.ofHom φ)))
    (he : e.hom ≫ pullback.snd M₀.toBase (Spec.map (CommRingCat.ofHom φ)) = M.toBase)
    (ψ : F₀ →+* F)

    (hsq : ∀ (U : M₀.C.Opens) [Nonempty (Scheme.Opens.toScheme U)]
        [Nonempty (Scheme.Opens.toScheme ((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ))) ⁻¹ᵁ U))] (s : Γ(M₀.C, U)),
      M.ffEquiv.symm (M.C.germToFunctionField ((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ))) ⁻¹ᵁ U) (((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ))).app U).hom s)) =
        ψ (M₀.ffEquiv.symm (M₀.C.germToFunctionField U s))) :

    (∀ y₀ : {q : Spec (CommRingCat.of κ) ⟶ M₀.C // q ≫ M₀.toBase = 𝟙 _}, ∃! y : {q : Spec (CommRingCat.of k) ⟶ M.C // q ≫ M.toBase = 𝟙 _},
      y.1 ≫ (e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ))) = Spec.map (CommRingCat.ofHom φ) ≫ y₀.1) ∧

    (∀ (y₀ : {q : Spec (CommRingCat.of κ) ⟶ M₀.C // q ≫ M₀.toBase = 𝟙 _}) (y : {q : Spec (CommRingCat.of k) ⟶ M.C // q ≫ M.toBase = 𝟙 _}),
      y.1 ≫ (e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ))) = Spec.map (CommRingCat.ofHom φ) ≫ y₀.1 →
      (M.pointEquivPlace y).toValuationSubring.comap ψ = (M₀.pointEquivPlace y₀).toValuationSubring ∧
        ∀ f : F₀, (M.pointEquivPlace y).ord (ψ f) = (M₀.pointEquivPlace y₀).ord f) ∧

    (∀ Q : Place k F,
      (∀ (y₀ : {q : Spec (CommRingCat.of κ) ⟶ M₀.C // q ≫ M₀.toBase = 𝟙 _}) (y : {q : Spec (CommRingCat.of k) ⟶ M.C // q ≫ M.toBase = 𝟙 _}),
        y.1 ≫ (e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ))) = Spec.map (CommRingCat.ofHom φ) ≫ y₀.1 → Q ≠ M.pointEquivPlace y) →
      ∀ f : F₀, f ≠ 0 → Q.ord (ψ f) = 0) := by sorry
