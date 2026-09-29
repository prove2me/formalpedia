-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_ramificationIndexAlong_eq_one_of_ord_eval_derivative_eq_zero
-- name    : AlgebraicCurve.Place.ramificationIndexAlong_eq_one_of_ord_eval_derivative_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/174f5b52-7092-552a-b07e-28a27a2f8c1c
-- title:
--   Simple-root criterion for unramifiedness of a place
-- statement:
--   Let $K$, $F$, $F'$ be fields with $F$ and $F'$ algebras over $K$, and let $\varphi : F \to F'$ be a $K$-algebra homomorphism whose underlying ring homomorphism is integral. Let $w$ be a place of $F'$ over $K$, that is, a valuation subring of $F'$ containing the image of $K$, different from $F'$ itself and a principal ideal ring; write $\operatorname{ord}_w$ for minus the logarithm of its associated adic valuation, and let $w_0 = w|_F$ be the place of $F$ whose valuation subring is the preimage under $\varphi$ of that of $w$. Let $z \in F'$ be such that every element of $F'$ is of the form $p^{\varphi}(z)$ for some $p \in F[X]$ (evaluation of $p$ at $z$ after applying $\varphi$ to the coefficients). Let $g \in F[X]$ be monic with all coefficients $w_0$-integral, $\operatorname{ord}_{w_0}(g_i) \ge 0$ for every $i$, and with $g^{\varphi}(z) = 0$. Assume moreover that $(g')^{\varphi}(z) \neq 0$ and $\operatorname{ord}_w\big((g')^{\varphi}(z)\big) = 0$. Then the ramification index of $w$ along $\varphi$ equals $1$, the index being defined as the infimum of the set of positive natural numbers $n$ for which there exists $f \in F$, $f \neq 0$, with $\operatorname{ord}_w(\varphi(f)) = n$.
--
--   This is the Dedekind–Hensel simple-root criterion in the form used for function fields: if $F'$ is generated over $F$ by a root of a monic polynomial with integral coefficients whose derivative is a unit at $w$, then $w$ is unramified over its restriction to $F$. It is applied in the analysis of the ramification of the inclusion of the function field of a modular curve of level $\Gamma_0(N)$, in three lemmas computing ramification indices from the order of vanishing of $j$-invariants.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_ramificationIndexAlong_eq_one_of_ord_eval_derivative_eq_zero.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AlgebraicCurve.Place.ramificationIndexAlong_eq_one_of_ord_eval_derivative_eq_zero
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (w : AlgebraicCurve.Place K F')

    (z : F') (hgen : ∀ x : F', ∃ p : Polynomial F, Polynomial.eval₂ φ.toRingHom z p = x)

    (g : Polynomial F) (hg : g.Monic)
    (hgO : ∀ i : ℕ, 0 ≤ (w.restrictAlong φ hφ).ord (g.coeff i))
    (hgz : Polynomial.eval₂ φ.toRingHom z g = 0)

    (hne : Polynomial.eval₂ φ.toRingHom z (Polynomial.derivative g) ≠ 0)
    (hsimple : w.ord (Polynomial.eval₂ φ.toRingHom z (Polynomial.derivative g)) = 0) :
    AlgebraicCurve.Place.ramificationIndexAlong φ w = 1 := by sorry
