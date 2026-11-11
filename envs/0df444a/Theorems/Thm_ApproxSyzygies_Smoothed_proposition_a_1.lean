-- Prove2me | Theorems.Thm_ApproxSyzygies_Smoothed_proposition_a_1
-- name    : ApproxSyzygies.Smoothed.proposition_a_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:03:09.190197+00:00
-- url     : https://prove2.me/theorems/e2f5faf6-c98d-48c2-b69c-e1182b652e6b
-- title:
--   Proposition A.1 — Bombieri norm: $\sum_\ell\|\partial p/\partial x_\ell\|^2=d^2\|p\|^2$, $\|\sum_\ell x_\ell p_\ell\|^2\le\sum_\ell\|p_\ell\|^2$, $\|pq\|\le\|p\|\|q\|$
-- statement:
--   Let $\|\cdot\|$ be the Bombieri norm on homogeneous polynomials in $x=(x_1,\dots,x_n)$, each polynomial normed in its own degree. Then:
--
--   1. for every $p\in\mathbb R[x]_{=d}$ (with $\partial p/\partial x_\ell\in\mathbb R[x]_{=d-1}$),
--   $$\sum_{\ell=1}^n\Big\|\frac{\partial p}{\partial x_\ell}\Big\|^2=d^2\|p\|^2;$$
--   2. for all $p_1,\dots,p_n\in\mathbb R[x]_{=d}$, $\big\|\sum_{\ell=1}^nx_\ell p_\ell\big\|^2\le\sum_{\ell=1}^n\|p_\ell\|^2$;
--   3. for all homogeneous $p\in\mathbb R[x]_{=d_1}$, $q\in\mathbb R[x]_{=d_2}$, $\|p\,q\|\le\|p\|\,\|q\|$.
--
--   These are the norm facts behind every operator-norm bound in §4: Euler's identity in Lemma 4.2 and the contractivity of multiplication in Lemmas 4.3 and 4.4.
--
--   Differences from the source:
--   - encoding: $\mathbb R[x]_{=d}$ with the Bombieri inner product; $\mathbb R[x]_{=d}=\{0\}$ for $d<0$ → `Hom σ d` = Euclidean space on the multi-indices $|\alpha|=d$ (empty for $d<0$), read as $\sum_\alpha p_\alpha\sqrt{d!/\alpha!}\,x^\alpha$ by `toPoly`; `ofPoly d f` reads a polynomial back; integer degrees; reason: the Bombieri-orthonormal coordinates make the Bombieri norm the Euclidean norm (p. 17); integer degrees give the zero space for negative degree with no truncated subtraction
-- source:
--   Bhaskara, Guo, Sinha, Srinivas, Vijayaraghavan, Approximate Syzygies of Smoothed Polynomials and Applications, STOC 2027 submission (manuscript sha256 9c17d04e…), pp. 83-84, Proposition A.1

import Mathlib
import Definitions.Def_ApproxSyzygies_Smoothed_Bombieri

open MvPolynomial

namespace ApproxSyzygies.Smoothed

/-- Proposition A.1 (pp. 83–84): properties of the Bombieri norm on homogeneous polynomials in
`n` variables. (1) `∑_ℓ ‖∂p/∂x_ℓ‖² = d² ‖p‖²` for `p ∈ ℝ[x]_{=d}` (each `∂p/∂x_ℓ` normed in
`ℝ[x]_{=d−1}`); (2) `‖∑_ℓ x_ℓ p_ℓ‖² ≤ ∑_ℓ ‖p_ℓ‖²` for `p_1, …, p_n ∈ ℝ[x]_{=d}`;
(3) `‖p q‖ ≤ ‖p‖ ‖q‖` for homogeneous `p, q` of any degrees. -/
theorem proposition_a_1 (n : ℕ) :
    (∀ (d : ℕ) (p : Hom (Fin n) (d : ℤ)),
      ∑ ℓ : Fin n, ‖ofPoly ((d : ℤ) - 1) (pderiv ℓ (toPoly p))‖ ^ 2 = (d : ℝ) ^ 2 * ‖p‖ ^ 2) ∧
    (∀ (d : ℕ) (p : Fin n → Hom (Fin n) (d : ℤ)),
      ‖ofPoly ((d : ℤ) + 1) (∑ ℓ : Fin n, X ℓ * toPoly (p ℓ))‖ ^ 2 ≤ ∑ ℓ : Fin n, ‖p ℓ‖ ^ 2) ∧
    (∀ (d₁ d₂ : ℕ) (p : Hom (Fin n) (d₁ : ℤ)) (q : Hom (Fin n) (d₂ : ℤ)),
      ‖ofPoly ((d₁ : ℤ) + d₂) (toPoly p * toPoly q)‖ ≤ ‖p‖ * ‖q‖) := by sorry

end ApproxSyzygies.Smoothed
