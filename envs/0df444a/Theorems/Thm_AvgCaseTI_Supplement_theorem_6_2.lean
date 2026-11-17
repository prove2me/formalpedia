-- Prove2me | Theorems.Thm_AvgCaseTI_Supplement_theorem_6_2
-- name    : AvgCaseTI.Supplement.theorem_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T11:37:03.539347+00:00
-- url     : https://prove2.me/theorems/4c60f07f-9f00-45fd-acad-0d1a6c391cee
-- title:
--   Theorem 6.2 — limiting proportion of matrices with prescribed $\mathbb F_q$-eigenvalue multiplicities
-- statement:
--   Let $\mathbb F_q$ be a finite field with $q$ elements and $m:\mathbb F_q\to\mathbb N$ a fixed function. Let $\alpha_m(n,q)$ be the proportion of matrices $A\in\mathrm M(n,q)$ whose characteristic polynomial is $f_0(t)\prod_{\lambda\in\mathbb F_q}(t-\lambda)^{m(\lambda)}$ with $f_0$ free of roots in $\mathbb F_q$. Then
--   $$
--   \alpha_m(\infty,q):=\lim_{n\to\infty}\alpha_m(n,q)=c(q)^q\cdot\prod_{\lambda\in\mathbb F_q}\frac{q^{-m(\lambda)}}{|c_{m(\lambda)}(q)|},
--   $$
--   where $c_k(q)=\prod_{i=1}^k(1-q^{-i})$ and $c(q)=\lim_k c_k(q)$.
--
--   This extends the Neumann–Praeger count of eigenvalue-free matrices ($m\equiv0$, limit $c(q)^q$) to any prescribed finite multiset of $\mathbb F_q$-eigenvalues.
--
--   Differences from the source:
--
--   - reading: m : F_q → N "satisfying D(m) = O(1)" → m : K → ℕ fixed, independent of n; reason: α_m(∞, q) is the limit in n for one function m; a fixed m has D(m) = Σ m(λ) constant
--   - encoding: lim_{n→∞} α_m(n, q) = … → Tendsto (alphaM K m) atTop (𝓝 …), K any finite field with q elements; reason: limits as Tendsto (reading R8); c(q) is the published cInf
-- source:
--   Li, Li, Qiao, Tao, Wang, On the average-case complexity landscape for Tensor-Isomorphism-complete problems over finite fields, arXiv:2604.00591 (held version sha256 baf552e1…), Theorem 6.2, p.36 (PDF p.38)

import Mathlib
import Definitions.Def_AvgCaseTI_cn
import Definitions.Def_AvgCaseTI_Supplement_alphaM

set_option autoImplicit false

namespace AvgCaseTI.Supplement

open AvgCaseTI Filter Topology

/-- **Theorem 6.2 (matrices with prescribed `F_q`-eigenvalue multiplicities).**

Li, Li, Qiao, Tao, Wang, arXiv:2604.00591 (held version sha256 baf552e1…), Theorem 6.2, p.36 (PDF p.38): "Let α_m(n, q) be defined as above with respect to some
function m : F_q → N satisfying D(m) = O(1). Then we have
α_m(∞, q) := lim_{n→∞} α_m(n, q) = c(q)^q · ∏_{λ∈F_q} q^{−m(λ)} / |c_{m(λ)}(q)|."

For every finite field `K` with `q` elements and every fixed `m : K → ℕ`,
`α_m(n, q) → c(q)^q · ∏_{λ ∈ K} q^{−m(λ)} / |c_{m(λ)}(q)|` as `n → ∞`.

**Formalization Note.** `m` does not depend on `n`, which is the hypothesis `D(m) = Σ_λ m(λ) = O(1)`.
`c_k(q) = cn q k` and `c(q) = cInf q`. -/
theorem theorem_6_2 {K : Type*} [Field K] [Fintype K] {q : ℕ} (hq : Fintype.card K = q)
    (m : K → ℕ) :
    Tendsto (alphaM K m) atTop
      (𝓝 (cInf q ^ q * ∏ a : K, (q : ℝ) ^ (-(m a : ℤ)) / |cn q (m a)|)) := by sorry

end AvgCaseTI.Supplement
