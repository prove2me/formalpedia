-- Prove2me | Theorems.Thm_AlgebraicCurve_kw_cart_C_pow_smul_D_eq_zero
-- name    : AlgebraicCurve.kw_cart_C_pow_smul_D_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/804b6e95-4d39-5790-9030-609967c59af3
-- title:
--   Cartier operator annihilates gⁱ dg for i+1<ℓ
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, let $\ell$ be a prime and suppose $F$ has characteristic $\ell$. Fix $t \in F$ such that the universal derivation satisfies $D_{F/K}(t) \neq 0$ in $\Omega[F\!\mid\!K]$ and the $F$-submodule spanned by $\{D_{F/K}(t)\}$ is the whole of $\Omega[F\!\mid\!K]$; assume further that every $x \in F$ is separable over the subfield underlying `kw_pke_expansionField`, i.e. the intermediate field obtained by adjoining $t$ to the subfield `kw_pke_pthPowers` $= F^{\ell}$ (the field range of the Frobenius endomorphism of $F$), and that the minimal polynomial of $t$ over $F^{\ell}$ has degree exactly $\ell$. Under these hypotheses `kw_cart_C` sends a differential $\omega$ to $r \cdot D_{F/K}(t)$, where $r$ is the $\ell$-th root (selected by `kw_cart_root`) of the coefficient of index $\ell - 1$ in the expansion, produced by `kw_cart_repr`, of the unique $u \in F$ with $\omega = u \cdot D_{F/K}(t)$ as $\sum_{j<\ell} c_j t^{j}$ with $c_j \in F^{\ell}$. The assertion is that for every $g \in F$ and every natural number $i$ with $i + 1 < \ell$ one has `kw_cart_C` $(g^{i} \cdot D_{F/K}(g)) = 0$.
--
--   This is the vanishing of the Cartier operator on the differentials $g^i\,dg$ with $i+1 < \ell$, one of the defining properties of the Cartier operator in characteristic $\ell$. It feeds into the verification that `kw_cart_C` satisfies the Cartier laws and into the uniqueness statement [`AlgebraicCurve.cartierOperator_existsUnique`](thm.html#AlgebraicCurve.cartierOperator_existsUnique) characterising the operator by those laws, via [`AlgebraicCurve.kw_cart_C_eq_of_cartierLaws`](thm.html#AlgebraicCurve.kw_cart_C_eq_of_cartierLaws).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_kw_cart_C_pow_smul_D_eq_zero.lean

import Definitions.Def_AlgebraicGeometry_KwCartierOperatorTCoordEngine

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.kw_cart_C_pow_smul_D_eq_zero {K F : Type*} [Field K] [Field F]
    [Algebra K F] {ℓ : ℕ} [Fact ℓ.Prime] [CharP F ℓ] (t : F)
    (hdt : KaehlerDifferential.D K F t ≠ 0)
    (hspan : Submodule.span F {KaehlerDifferential.D K F t} = ⊤)
    (hsep : ∀ x : F,
      IsSeparable (AlgebraicCurve.KwPke.kw_pke_expansionField (ℓ := ℓ) t).toSubfield x)
    (hdeg : (minpoly (AlgebraicCurve.KwPke.kw_pke_pthPowers F ℓ) t).natDegree = ℓ)
    (g : F) {i : ℕ} (hi : i + 1 < ℓ) :
    AlgebraicCurve.KwCart.kw_cart_C (K := K) t hdt hspan hsep hdeg
      (g ^ i • KaehlerDifferential.D K F g) = 0 := by sorry
