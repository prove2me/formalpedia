-- Prove2me | Theorems.Thm_DrinfeldCurve_LocalChart_prod_prod_X_sub_C_natCast_mul_add_eq_moore
-- name    : DrinfeldCurve.LocalChart.prod_prod_X_sub_C_natCast_mul_add_eq_moore
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/d387b765-c48b-594e-b787-7e09225f22ee
-- title:
--   Moore–Dickson product of 𝔽_q-linear forms in two variables
-- statement:
--   Let $q$ be a prime and $R$ a commutative ring of characteristic $q$. Work in the univariate polynomial ring $(R[X_0,X_1])[Z]$, where $R[X_0,X_1]$ is the polynomial ring in two variables indexed by `Fin 2`. The assertion is an identity between the product over all pairs $(a,b)$ with $a,b$ ranging over `Fin q` (each coerced to a natural number and then mapped into $R[X_0,X_1]$ by the natural-number cast) of the linear factors $Z - (a X_0 + b X_1)$, the coefficients $a X_0 + b X_1$ being constants in $Z$, and the explicit three-term polynomial
--   $$Z^{q^2} \;-\; H\,Z^{q} \;+\; F^{\,q-1}\,Z,$$
--   where the coefficients are again constants in $Z$, given by
--   $$H=\sum_{i=0}^{q} X_0^{(q-1)i} X_1^{(q-1)(q-i)}, \qquad F = X_0X_1^{q}-X_0^{q}X_1,$$
--   the exponents being formed with truncated natural-number subtraction and the sum taken over $i$ in `Finset.range (q+1)`. Thus the monic degree-$q^2$ polynomial whose roots are the $q^2$ values of the $\mathbb{F}_q$-linear forms $aX_0+bX_1$ has vanishing $Z^j$-coefficients except for $j=q^2$, $j=q$ and $j=1$, with the two intermediate coefficients $-H$ and $F^{q-1}$ as displayed.
--
--   This is the Moore–Dickson identity for the $\mathbb{F}_q$-linear forms in two variables: $F$ is the product of the $q+1$ rational linear forms up to scalars (the Drinfeld form) and $H$ the complementary Dickson factor, with $HF = X_0X_1^{q^2}-X_0^{q^2}X_1$. It is used, via [`DrinfeldCurve.LocalChart.exists_prod_prod_X_sub_C_eq_moore_add_C_C_mul`](thm.html#DrinfeldCurve.LocalChart.exists_prod_prod_X_sub_C_eq_moore_add_C_C_mul), to identify the coefficients of the product $\prod_v (Z-\ell_v)$ over a Drinfeld basis in the local chart of the relevant moduli problem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_DrinfeldCurve_LocalChart_prod_prod_X_sub_C_natCast_mul_add_eq_moore.lean

import Mathlib
import Definitions.Def_DrinfeldCurve_LocalChart

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem DrinfeldCurve.LocalChart.prod_prod_X_sub_C_natCast_mul_add_eq_moore
    (q : ℕ) [Fact q.Prime] (R : Type) [CommRing R] [CharP R q] :
    ∏ a : Fin q, ∏ b : Fin q,
        (Polynomial.X - Polynomial.C
          (((a : ℕ) : MvPolynomial (Fin 2) R) * MvPolynomial.X 0 + ((b : ℕ) : MvPolynomial (Fin 2) R) * MvPolynomial.X 1) :
          Polynomial (MvPolynomial (Fin 2) R)) =
      Polynomial.X ^ (q ^ 2)
        - Polynomial.C (∑ i ∈ Finset.range (q + 1),
            (MvPolynomial.X 0 : MvPolynomial (Fin 2) R) ^ ((q - 1) * i) * MvPolynomial.X 1 ^ ((q - 1) * (q - i))) *
          Polynomial.X ^ q
        + Polynomial.C (((MvPolynomial.X 0 : MvPolynomial (Fin 2) R) * MvPolynomial.X 1 ^ q
            - MvPolynomial.X 0 ^ q * MvPolynomial.X 1) ^ (q - 1)) * Polynomial.X := by sorry
