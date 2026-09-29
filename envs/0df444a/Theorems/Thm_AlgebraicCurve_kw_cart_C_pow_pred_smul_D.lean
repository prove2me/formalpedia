-- Prove2me | Theorems.Thm_AlgebraicCurve_kw_cart_C_pow_pred_smul_D
-- name    : AlgebraicCurve.kw_cart_C_pow_pred_smul_D
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/62e4142c-a595-5c77-afe5-c56c4e1a4d2c
-- title:
--   Cartier operator fixes g^{ℓ-1} dg
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, let $\ell$ be a prime and suppose $F$ has characteristic $\ell$. Let $t \in F$ be such that the Kähler differential $D_{K/F}t \in \Omega[F/K]$ is nonzero and spans $\Omega[F/K]$ as an $F$-module, so that $\Omega[F/K]$ is free of rank one on $dt$. Assume further that every $x \in F$ is separable over the subfield underlying the intermediate field $\mathrm{kw\_pke\_expansionField}\,t$, namely the subfield of $F$ generated over $\mathrm{kw\_pke\_pthPowers}\,F\,\ell =$ the image of the Frobenius endomorphism $x \mapsto x^{\ell}$ by adjoining $t$, and that the minimal polynomial of $t$ over that field of $\ell$-th powers has degree $\ell$. Then for every $g \in F$ the operator $\mathrm{kw\_cart\_C}$ — which sends $\omega$ to $c \cdot dt$, where $c$ is a chosen $\ell$-th root of the coefficient of $t^{\ell-1}$ in a chosen expansion over the field of $\ell$-th powers of the chosen $F$-coordinate of $\omega$ with respect to $dt$ — satisfies $\mathrm{kw\_cart\_C}\,(g^{\ell-1} \cdot dg) = dg$.
--
--   This is the third of the classical defining identities of the Cartier operator in characteristic $\ell$, stating that $g^{\ell-1}\,dg$ is fixed, with no hypothesis on $g$ (for $g = 0$ both sides vanish). Together with additivity and $\ell$-semilinearity it feeds the characterisation of the Cartier operator by its defining laws, being cited by [`AlgebraicCurve.cartierOperator_existsUnique`](thm.html#AlgebraicCurve.cartierOperator_existsUnique) and [`AlgebraicCurve.kw_cart_C_eq_of_cartierLaws`](thm.html#AlgebraicCurve.kw_cart_C_eq_of_cartierLaws).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_kw_cart_C_pow_pred_smul_D.lean

import Definitions.Def_AlgebraicGeometry_KwCartierOperatorTCoordEngine

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.kw_cart_C_pow_pred_smul_D {K F : Type*} [Field K] [Field F]
    [Algebra K F] {ℓ : ℕ} [Fact ℓ.Prime] [CharP F ℓ] (t : F)
    (hdt : KaehlerDifferential.D K F t ≠ 0)
    (hspan : Submodule.span F {KaehlerDifferential.D K F t} = ⊤)
    (hsep : ∀ x : F,
      IsSeparable (AlgebraicCurve.KwPke.kw_pke_expansionField (ℓ := ℓ) t).toSubfield x)
    (hdeg : (minpoly (AlgebraicCurve.KwPke.kw_pke_pthPowers F ℓ) t).natDegree = ℓ)
    (g : F) :
    AlgebraicCurve.KwCart.kw_cart_C (K := K) t hdt hspan hsep hdeg
      (g ^ (ℓ - 1) • KaehlerDifferential.D K F g) = KaehlerDifferential.D K F g := by sorry
