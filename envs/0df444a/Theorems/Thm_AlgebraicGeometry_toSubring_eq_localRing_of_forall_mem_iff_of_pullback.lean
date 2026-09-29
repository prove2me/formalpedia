-- Prove2me | Theorems.Thm_AlgebraicGeometry_toSubring_eq_localRing_of_forall_mem_iff_of_pullback
-- name    : AlgebraicGeometry.toSubring_eq_localRing_of_forall_mem_iff_of_pullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/998a5d21-15d9-5a14-9f01-5eeec4e45d0f
-- title:
--   Valuation ring pinned by its trace on K(X₀)
-- statement:
--   Let $L$ be a field and $A\subseteq L$ a valuation subring satisfying: for all $a,b\in A$ with $a$ in the maximal ideal and $b\neq 0$ there is $n\in\mathbb N$ with $b\mid a^{n}$, and $A\neq L$ as sets. Let $A_0$ be a commutative ring with a ring map $\iota:A_0\to A$, let $X_0$ be an integral scheme over $\operatorname{Spec} A_0$ via $\mathrm{toBase}_0$, let $F$ be a field that is an $L$-algebra, and let $X$ be an integral scheme with a proper morphism $\mathrm{toBase}:X\to\operatorname{Spec} A$. Assume a ring isomorphism $\varphi:F\simeq K(X)$ (the stalk at the generic point) with $\varphi(a)=$ the germ at the generic point of the image of $a\in A$ under $\mathrm{toBase}$ on global sections, for all $a\in A$. Assume an isomorphism $\mathrm{iso}:X\cong X_0\times_{\operatorname{Spec}A_0}\operatorname{Spec}A$ whose composite with the second projection is $\mathrm{toBase}$, write $\mathrm{pr}$ for its composite with the first projection, and assume $\mathrm{pr}$ sends the generic point of $X$ to that of $X_0$. Assume a ring map $j_0:K(X_0)\to F$ with $\varphi\circ j_0$ equal to the composite of the specialisation map $K(X_0)\to\mathcal O_{X_0,\mathrm{pr}(\text{gen})}$ with the stalk map of $\mathrm{pr}$ at the generic point, and assume every element of $F$ is algebraic over the subring $j_0(K(X_0))$. Let $\eta\in X$ lie over the closed point of $\operatorname{Spec}A$ and be the only point of that fibre with the given image under $\mathrm{pr}$, and assume the image in $F$ under $\varphi^{-1}$ of $\mathcal O_{X,\eta}$ (i.e. the range of $\varphi^{-1}\circ(\mathcal O_{X,\eta}\to K(X))$) is the underlying subring of some valuation subring of $F$. Then for any valuation subring $O$ of $F$ containing the image of $A$ and such that, for $g\in K(X_0)$, $j_0(g)\in O$ holds exactly when $g$ lies in the image of $\mathcal O_{X_0,\mathrm{pr}(\eta)}\to K(X_0)$, the underlying subring of $O$ equals that image of $\mathcal O_{X,\eta}$ in $F$.
--
--   This is a uniqueness statement for the prolongation of a valuation along the base change $X\cong X_0\times_{\operatorname{Spec}A_0}\operatorname{Spec}A$: a valuation ring of the large function field $F$ is determined by its trace on $K(X_0)$ once the relevant point of the special fibre is alone in its $\mathrm{pr}$-fibre, the centre being produced by the valuative criterion of properness. It is used in the construction of the semistable scheme model of the full-level modular curve, to identify the local rings at the generic points of the components of the special fibre with prescribed valuation rings of $F$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_toSubring_eq_localRing_of_forall_mem_iff_of_pullback.lean

import Definitions.Def_AlgebraicCurve_SemistableModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.toSubring_eq_localRing_of_forall_mem_iff_of_pullback
    {L : Type} [Field L] (A : ValuationSubring L)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (hA : (A : Set L) ≠ Set.univ)
    (A₀ : Type) [CommRing A₀] (ι : A₀ →+* ↥A)
    (X₀ : Scheme.{0}) (toBase₀ : X₀ ⟶ Spec (CommRingCat.of A₀)) [IsIntegral X₀]
    {F : Type} [Field F] [Algebra L F]
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A)) [IsIntegral X] [IsProper toBase]
    (φ : F ≃+* X.functionField)
    (hφ : ∀ a : ↥A, φ (algebraMap L F (a : L)) = SemistableModel.baseToFunctionField toBase a)
    (iso : X ≅ Limits.pullback toBase₀ (Spec.map (CommRingCat.ofHom ι)))
    (hiso : iso.hom ≫ Limits.pullback.snd toBase₀ (Spec.map (CommRingCat.ofHom ι)) = toBase)
    (hgen : (iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base (genericPoint X) = genericPoint X₀)
    (j₀ : X₀.functionField →+* F)
    (hj₀ : ∀ g : X₀.functionField, φ (j₀ g) =
      ((iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).stalkMap (genericPoint X)).hom
        ((X₀.presheaf.stalkSpecializes (specializes_of_eq hgen)).hom g))
    (halgF : ∀ f : F, IsAlgebraic ↥(j₀.range) f)
    (η : X) (hη : toBase.base η = closedPoint ↥A)
    (hfib : ∀ x : X, toBase.base x = closedPoint ↥A →
      (iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base x =
        (iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base η → x = η)
    (hV : ∃ V : ValuationSubring F, V.toSubring = SemistableModel.localRing X φ η)
    (O : ValuationSubring F) (hOA : ∀ a : ↥A, algebraMap L F (a : L) ∈ O)
    (hOtr : ∀ g : X₀.functionField, j₀ g ∈ O ↔
      g ∈ (algebraMap (X₀.presheaf.stalk
              ((iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base η))
            X₀.functionField).range) :
    O.toSubring = SemistableModel.localRing X φ η := by sorry
