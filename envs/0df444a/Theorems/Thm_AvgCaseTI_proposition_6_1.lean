-- Prove2me | Theorems.Thm_AvgCaseTI_proposition_6_1
-- name    : AvgCaseTI.proposition_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:44:45.350265+00:00
-- url     : https://prove2.me/theorems/60033828-0837-4d68-94c6-6a36b39a5467
-- title:
--   Proposition 6.1 — Neumann–Praeger: eigenvalue-free and unipotent proportions
-- statement:
--   Let $\mathbb F_q$ be a finite field, $v(\mathrm{GL},n,q)$ and $u(\mathrm{GL},n,q)$ the proportions of eigenvalue-free and of unipotent matrices in $\mathrm{GL}(n,q)$, and
--   $$
--   V(z)=\sum_{n\ge0}v(\mathrm{GL},n,q)z^n,\qquad U(z)=\sum_{n\ge0}u(\mathrm{GL},n,q)z^n .
--   $$
--   Then
--   1. $V(z)\,U(z)^{q-1}=(1-z)^{-1}$;
--   2. $u(\mathrm{GL},n,q)=\dfrac{1}{c_n(q)\,q^n}$ for every $n$;
--   3. $v(\mathrm{GL},n,q)\to v(\mathrm{GL},\infty,q)=c(q)^{q-1}$, and whenever $n>5(q-1)^2$,
--   $$
--   v(\mathrm{GL},\infty,q)-v(\mathrm{GL},n,q)=(-1)^{n+1}\varepsilon_n,\qquad 0<\varepsilon_n<\tfrac12\,16^{q-1}q^{-\frac{(n+1)(n+q)}{2(q-1)}}.
--   $$
--
--   The paper cites these from Neumann and Praeger [NP98, Theorems 4.1–4.3]; they are the input for the counts of matrices with prescribed eigenvalue multiplicities in §6.
--
--   **Formalization Note** $V,U$ are formal power series over $\mathbb R$, and clause 1 is written $V\,U^{q-1}(1-z)=1$. In clause 3, $\varepsilon_n=(-1)^{n+1}\bigl(c(q)^{q-1}-v(\mathrm{GL},n,q)\bigr)$.
--
--   Differences from the source:
--
--   - encoding: generating functions V(GL,q,z), U(GL,q,z) and the identity V·U^{q−1} = (1 − z)^{−1} → formal power series over ℝ with V·U^{q−1}·(1 − X) = 1; reason: the identity of power series; same coefficients
--   - encoding: v(GL,∞,q) := lim v(GL,n,q), and "= (−1)^{n+1} ε_n with 0 < ε_n < …" → `Tendsto` to c(q)^{q−1}, and the bounds on (−1)^{n+1}(c(q)^{q−1} − v(GL,n,q)); reason: ε_n is determined by the displayed equation; same content
--   - encoding: c(q) = lim c_n(q) (an infinite product) → `cInf q`, the infimum of the decreasing positive partial products → same value; reason: Lean convention
-- source:
--   Li, Li, Qiao, Tao, Wang, On the average-case complexity landscape for Tensor-Isomorphism-complete problems over finite fields, arXiv:2604.00591 (held version sha256 baf552e1…), Proposition 6.1, pp.35–36 (PDF pp.37–38)

import Mathlib
import Definitions.Def_AvgCaseTI_cn
import Definitions.Def_AvgCaseTI_vGL

set_option autoImplicit false

namespace AvgCaseTI

open Filter Topology

/-- **Proposition 6.1 (Neumann–Praeger: eigenvalue-free and unipotent proportions in `GL(n, q)`).**

Li, Li, Qiao, Tao, Wang, arXiv:2604.00591 (held version sha256 baf552e1…), Proposition 6.1,
pp.35–36 (PDF pp.37–38), citing [NP98, Theorems 4.1–4.3]. For every finite field with `q`
elements, with `V(z) = Σ v(GL, n, q) zⁿ`, `U(z) = Σ u(GL, n, q) zⁿ`:
1. `V(z)·U(z)^{q−1} = (1 − z)^{−1}`;
2. `u(GL, n, q) = 1/(c_n(q)·qⁿ)` for every `n`;
3. `v(GL, n, q) → c(q)^{q−1}`, and for `n > 5(q − 1)²`,
   `v(GL, ∞, q) − v(GL, n, q) = (−1)^{n+1} ε_n` with
   `0 < ε_n < ½·16^{q−1}·q^{−(n+1)(n+q)/(2(q−1))}`.

**Formalization Note.** `V`, `U` are formal power series over `ℝ`; clause 1 is written
`V·U^{q−1}·(1 − X) = 1`. In clause 3, `ε_n = (−1)^{n+1}(c(q)^{q−1} − v(GL, n, q))`. -/
theorem proposition_6_1 {K : Type*} [Field K] [Fintype K] {q : ℕ} (hq : Fintype.card K = q) :
    PowerSeries.mk (vGL K) * PowerSeries.mk (uGL K) ^ (q - 1) * (1 - PowerSeries.X) = 1 ∧
    (∀ n : ℕ, uGL K n = 1 / (cn q n * (q : ℝ) ^ n)) ∧
    Tendsto (vGL K) atTop (𝓝 (cInf q ^ (q - 1))) ∧
    ∀ n : ℕ, 5 * (q - 1) ^ 2 < n →
      0 < (-1 : ℝ) ^ (n + 1) * (cInf q ^ (q - 1) - vGL K n) ∧
      (-1 : ℝ) ^ (n + 1) * (cInf q ^ (q - 1) - vGL K n) <
        1 / 2 * (16 : ℝ) ^ (q - 1) *
          (q : ℝ) ^ (-(((n : ℝ) + 1) * ((n : ℝ) + q)) / (2 * ((q : ℝ) - 1))) := by sorry

end AvgCaseTI
