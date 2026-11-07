-- Prove2me | Theorems.Thm_AvgCaseTI_proposition_2_1
-- name    : AvgCaseTI.proposition_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:42:16.724208+00:00
-- url     : https://prove2.me/theorems/efe73a59-703f-443d-ad17-18c59976649f
-- title:
--   Proposition 2.1 — $|\mathrm{GL}(n,q)|$, $c_n(q)\to c(q)\in(1/4,1)$ and its rate
-- statement:
--   Let $\mathbb F_q$ be a finite field and $c_n(q)=\prod_{i=1}^{n}(1-q^{-i})$. Then:
--   1. for every $n\ge0$, $\displaystyle |\mathrm{GL}(n,q)|=\prod_{i=0}^{n-1}(q^n-q^i)$;
--   2. for every $n$, $\displaystyle \frac{|\mathrm{GL}(n,q)|}{|\mathrm M(n,q)|}=\prod_{i=0}^{n-1}(1-q^{i-n})=c_n(q)$;
--   3. $c_n(q)$ converges to a constant $c(q)$, and $1/4<c(q)<1$;
--   4. for every $n$,
--   $$
--   |c(q)-c_n(q)|=c_n(q)\Bigl|1-\prod_{i=n+1}^{\infty}(1-q^{-i})\Bigr|\le\frac{q^{-(n+1)}}{(1-q^{-1})(1-q^{-(n+1)})}\le4q^{-(n+1)}.
--   $$
--
--   The constant $c(q)$ is the limiting probability that a uniform matrix over $\mathbb F_q$ is invertible; every limiting probability of the mission is expressed through it.
--
--   **Formalization Note** $c(q)$ is the infimum of the partial products (clause 3 states that it is their limit), and the infinite tail product is likewise the infimum of its partial products.
--
--   Differences from the source:
--
--   - encoding: c(q) = lim c_n(q) (an infinite product) → `cInf q`, the infimum of the decreasing positive partial products → same value; clause 3 states the convergence; reason: Lean convention; a decreasing positive sequence converges to its infimum
--   - encoding: ∏_{i=n+1}^∞ (1 − q^{−i}) → `tailProd q n`, the infimum of the partial products; reason: same value; avoids a junk value of an unconditioned infinite product
-- source:
--   Li, Li, Qiao, Tao, Wang, On the average-case complexity landscape for Tensor-Isomorphism-complete problems over finite fields, arXiv:2604.00591 (held version sha256 baf552e1…), Proposition 2.1, Eqs. (2)–(3), p.13 (PDF p.15)

import Mathlib
import Definitions.Def_AvgCaseTI_cn
import Definitions.Def_AvgCaseTI_hull

set_option autoImplicit false

namespace AvgCaseTI

open Filter Topology

/-- **Proposition 2.1 (order of `GL(n, q)`, the ratio `c_n(q)` and its limit `c(q)`).**

Li, Li, Qiao, Tao, Wang, arXiv:2604.00591 (held version sha256 baf552e1…), Proposition 2.1, p.13
(PDF p.15). For every finite field `K` with `q` elements:
1. `|GL(n, q)| = ∏_{i=0}^{n−1} (q^n − q^i)` for every `n`;
2. `c_n(q) := |GL(n, q)| / |M(n, q)| = ∏_{i=0}^{n−1} (1 − q^{i−n}) = ∏_{i=1}^{n} (1 − q^{−i})`;
3. `c_n(q)` converges to `c(q)`, and `1/4 < c(q) < 1`;
4. `|c(q) − c_n(q)| = c_n(q)·|1 − ∏_{i=n+1}^{∞}(1 − q^{−i})|
   ≤ q^{−(n+1)} / ((1 − q^{−1})(1 − q^{−(n+1)})) ≤ 4 q^{−(n+1)}` for every `n`.

**Formalization Note.** `c(q)` is `cInf q`, the infimum of the decreasing partial products; clause 3
says it is their limit. The infinite tail product is `tailProd q n`. Clause 1 is Mathlib's
`Matrix.card_GL_field` (`n` indexes over `Finset.range n`). -/
theorem proposition_2_1 {K : Type*} [Field K] [Fintype K] {q : ℕ} (hq : Fintype.card K = q) :
    (∀ n : ℕ, Nat.card (GL (Fin n) K) = ∏ i ∈ Finset.range n, (q ^ n - q ^ i)) ∧
    (∀ n : ℕ, (Nat.card (GL (Fin n) K) : ℝ) / Nat.card (Mat K n) = cn q n ∧
      cn q n = ∏ i ∈ Finset.range n, (1 - (q : ℝ) ^ ((i : ℤ) - n))) ∧
    Tendsto (cn q) atTop (𝓝 (cInf q)) ∧ 1 / 4 < cInf q ∧ cInf q < 1 ∧
    ∀ n : ℕ,
      |cInf q - cn q n| = cn q n * |1 - tailProd q n| ∧
      cn q n * |1 - tailProd q n| ≤
        (q : ℝ) ^ (-((n : ℤ) + 1)) / ((1 - (q : ℝ)⁻¹) * (1 - (q : ℝ) ^ (-((n : ℤ) + 1)))) ∧
      (q : ℝ) ^ (-((n : ℤ) + 1)) / ((1 - (q : ℝ)⁻¹) * (1 - (q : ℝ) ^ (-((n : ℤ) + 1)))) ≤
        4 * (q : ℝ) ^ (-((n : ℤ) + 1)) := by sorry

end AvgCaseTI
