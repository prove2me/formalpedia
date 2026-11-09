-- Prove2me | Theorems.Thm_CSPSubsample_claim_4_3
-- name    : CSPSubsample.claim_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:19:13.274922+00:00
-- url     : https://prove2.me/theorems/12356c09-b14c-43c8-a220-f38e96cfd7e0
-- title:
--   Claim 4.3 — factorial moments of the multinomial distribution
-- statement:
--   Let $(N_j)_{j\in[d]}\sim\mathrm{Multinomial}(N,y)$ with $y\in\Delta_d$, i.e. $y_j\ge0$ and $\sum_jy_j=1$. For nonnegative integers $g_1,\dots,g_d$ with $g=\sum_{j=1}^dg_j$,
--   $$
--   \mathbb E\Big[\prod_{j=1}^dN_j^{\underline{g_j}}\Big]=N^{\underline g}\prod_{i=1}^dy_i^{g_i},
--   $$
--   where $m^{\underline r}=m(m-1)\cdots(m-r+1)$ is the falling factorial. The paper cites this identity (Mosimann 1962; Ouimet 2021) and uses it to compute $\mathbb E[f(Z)]$ exactly in Lemma 4.4.
--
--   Differences from the source:
--   - encoding: E under (N_j) ∼ Multinomial(N, y) → the sum over draw sequences s ∈ [d]^N weighted by ∏_t y_{s_t}, with N_j = #{t : s_t = j}; reason: the multinomial law is the law of the counts of N i.i.d. draws from y; same expectation
-- source:
--   Bernasconi, Castiglioni, Celli, Farina, Malavolta, A Subsampling Theorem for Constraint Satisfaction Problems with Large Arity, arXiv:2608.00203 (PDF sha256 fd9ae01113266fee273c46c14c8a1a39f36a958dba3fc276cd74bf4c3daff445), Claim 4.3, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_CSPSubsample_multinomialExp

set_option autoImplicit false

namespace CSPSubsample

/-- **Claim 4.3** ([Mos62; Oui21]; arXiv:2608.00203 (PDF sha256 fd9ae011…), p.10 = PDF p.12).
Let `(N_j)_{j ∈ [d]} ∼ Multinomial(N, y)` with `y ∈ Δ_d`. For nonnegative integers
`g_1, …, g_d` with `g = ∑_j g_j`,
`E[∏_{j=1}^d N_j^{\underline{g_j}}] = N^{\underline g} ∏_{i=1}^d y_i^{g_i}`.

**Formalization Note** All three exponents on falling-factorial terms are falling factorials
(`Nat.descFactorial`); `y_i^{g_i}` is a power. `y ∈ Δ_d` is `y_j ≥ 0`, `∑_j y_j = 1`. The
multinomial expectation is the weighted sum over draw sequences (`multinomialExp`). -/
theorem claim_4_3 (d N : ℕ) (y : Fin d → ℝ) (hy0 : ∀ j, 0 ≤ y j) (hy1 : ∑ j, y j = 1)
    (g : Fin d → ℕ) :
    multinomialExp d N y (fun c => ∏ j, ((c j).descFactorial (g j) : ℝ)) =
      (N.descFactorial (∑ j, g j) : ℝ) * ∏ i, y i ^ g i := by sorry

end CSPSubsample
