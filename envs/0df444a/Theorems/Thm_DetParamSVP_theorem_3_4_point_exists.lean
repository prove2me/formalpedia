-- Prove2me | Theorems.Thm_DetParamSVP_theorem_3_4_point_exists
-- name    : DetParamSVP.theorem_3_4_point_exists
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:50:56.230195+00:00
-- url     : https://prove2.me/theorems/f26163ea-0bd8-4b85-8fa5-b47995d6a9a9
-- title:
--   Proof of Theorem 3.4, pp.22–23 — a point satisfying Eq. (9) with $g\ne0$ (via Lemma 2.19)
-- statement:
--   Fix $p\ge1$ and positive integers $m,d,D,h,k$ with $D\ge2$, $k\ge2$, $d^p\le h$ and $D^p<2k$; put $L=k-1$ and let $T$ be the bound of Eq. (7). Let $q>T$ be prime, let $y_1,\dots,y_L,x_1,\dots,x_m\in\mathbb F_q$ be distinct, and let $u\in\mathbb Z^m$ be nonzero with $\|u\|_p\le d$. Then there is a point $(z_1,\dots,z_L,\tau)\in\mathbb F_q^{L+1}$ satisfying
--
--   $$\sum_{\ell=1}^{L}(z_\ell^j-y_\ell^j)-\sum_{i\in I}u_i\big((x_i+\tau)^j-x_i^j\big)=0\qquad(1\le j\le L)\tag{9}$$
--
--   and $g(z_1,\dots,z_L,\tau)\ne0$, where $I$ is the support of $u$ and $g$ is the polynomial of Eq. (10).
--
--   For such a point the vector $w$ of Eq. (8) lies in $\mathcal L_{q,k}-s$, and by Claim 2 it satisfies $w|_S=u$ and $\|w\|_p^p\le W$.
--
--   Differences from the source:
--   - generalization: a prime q with T < q < 2T (chosen by Lemma 2.12) → any prime q > T; reason: the upper bound 2T matters only for the running time; the source q satisfies the hypothesis
--   - encoding: distinct y₁, …, y_L, x₁, …, x_m → injectivity of Sum.elim y x; reason: same condition
--   - encoding: the point (z₁, …, z_L, τ) and the variables Z₁, …, Z_L, Y → Fin.snoc z τ, variables Fin (L + 1) with Y the last; reason: reindexing
-- source:
--   Hirahara–Lin–Liu–Ogitsuka, Deterministic Parameterized Inapproximability of the Shortest Vector and Minimum Distance Problems, STOC 2027 submission (manuscript sha256 4584f5e2…), proof of Theorem 3.4, pp.22–23 (Eqs. (7), (9), (10))

import Definitions.Def_DetParamSVP_LpNorm
import Definitions.Def_DetParamSVP_RSConstruction

set_option autoImplicit false

namespace DetParamSVP

open MvPolynomial

/-- **Proof of Theorem 3.4: the point given by Lemma 2.19.** Under the hypotheses of Theorem 3.4
(positive integers `m, d, D, h, k` with `D ≥ 2`, `k ≥ 2`, `d^p ≤ h`, `D^p < 2k`), for a prime
`q > T` (`T` of Eq. (7)), distinct `y₁, …, y_L, x₁, …, x_m ∈ F_q` (`L = k − 1`) and a nonzero
`u ∈ ℤ^m` with `‖u‖_p ≤ d`, there is a point `(z₁, …, z_L, τ) ∈ F_q^{L+1}` satisfying Equation (9)
(for `1 ≤ j ≤ L`) and `g(z₁, …, z_L, τ) ≠ 0`, with `g` of Eq. (10).

Hirahara–Lin–Liu–Ogitsuka, *Deterministic Parameterized Inapproximability of the Shortest Vector
and Minimum Distance Problems*, STOC 2027 submission (manuscript sha256 4584f5e2…), proof of Theorem 3.4, pp.22–23.

**Formalization Note.** "Distinct `y₁, …, y_L, x₁, …, x_m`" is injectivity of `Sum.elim y x`. The
paper also has `q < 2T`, which matters only for the running time; here `q` is any prime above
`T`. The point is `Fin.snoc z τ` (`Z_ℓ = z_ℓ`, `Y = τ`). -/
theorem theorem_3_4_point_exists (p : ℝ) (hp : 1 ≤ p) (m d D h k : ℕ) (hm : 0 < m) (hd : 0 < d)
    (hD0 : 0 < D) (hh : 0 < h) (hk0 : 0 < k) (hD : 2 ≤ D) (hk : 2 ≤ k) (hdh : (d : ℝ) ^ p ≤ h)
    (hDk : (D : ℝ) ^ p < 2 * k) (q : ℕ) [Fact q.Prime] (hT : Tbound m D h k < q)
    (y : Fin (k - 1) → ZMod q) (x : Fin m → ZMod q) (hyx : Function.Injective (Sum.elim y x))
    (u : Fin m → ℤ) (hu : u ≠ 0) (hud : lpNorm p u ≤ d) :
    ∃ (z : Fin (k - 1) → ZMod q) (τ : ZMod q),
      (∀ j : ℕ, 1 ≤ j → j ≤ k - 1 → eval (Fin.snoc z τ) (eq9Poly y u x j) = 0) ∧
      eval (Fin.snoc z τ) (gPoly (k - 1) u x) ≠ 0 := by sorry

end DetParamSVP
