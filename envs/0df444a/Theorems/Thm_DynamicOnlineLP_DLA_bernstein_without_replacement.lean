-- Prove2me | Theorems.Thm_DynamicOnlineLP_DLA_bernstein_without_replacement
-- name    : DynamicOnlineLP.DLA.bernstein_without_replacement
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T19:37:59.323983+00:00
-- url     : https://prove2.me/theorems/f774ecb3-9a9b-490c-b64d-0e3995c062df
-- title:
--   Lemma 10 — Hoeffding–Bernstein inequality for sampling without replacement
-- statement:
--   Let $c_1,\dots,c_R$ be real numbers ($R\ge1$), with mean $\bar c=\frac1R\sum_i c_i$, variance $\sigma_R^2=\frac1R\sum_{i=1}^R(c_i-\bar c)^2$ and range $\Delta_R=\max_ic_i-\min_ic_i$. Let $u_1,\dots,u_r$ ($r\le R$) be a sample drawn without replacement from $\{c_1,\dots,c_R\}$. Then for every $t>0$,
--
--   $$\mathbb P\Big(\Big|\sum_{i=1}^r u_i-r\bar c\Big|\ge t\Big)\le 2\exp\Big(-\frac{t^2}{2r\sigma_R^2+t\Delta_R}\Big).$$
--
--   The paper quotes this from van der Vaart and Wellner (1996, Theorem 2.14.19) and uses it for every concentration step of its analysis (Lemmas 2, 5, 6 and inequality (14)).
--
--   **Formalization Note** The sample is the first $r$ entries $c_{\sigma(1)},\dots,c_{\sigma(r)}$ of a uniformly random permutation $\sigma$ of $\{1,\dots,R\}$, and the probability is the fraction of the $R!$ permutations at which the event holds. $\max$ and $\min$ are finite suprema and infima over the nonempty index set. In the degenerate case $\Delta_R=0$ the right-hand side's denominator is $0$; Lean's convention $x/0=0$ then gives the bound $2$, while the event has probability $0$.
-- source:
--   Agrawal, Wang, Ye, A Dynamic Near-Optimal Algorithm for Online Linear Programming, Oper. Res. 62(4), 2014, p. 887, Appendix A.1, Lemma 10 (from van der Vaart and Wellner 1996, Theorem 2.14.19)

import Mathlib
import Definitions.Def_DynamicOnlineLP_DLA_Instance

namespace DynamicOnlineLP.DLA

/-- Lemma 10 (Agrawal–Wang–Ye 2014, p. 887; van der Vaart and Wellner 1996, Theorem 2.14.19):
Hoeffding–Bernstein inequality for sampling without replacement. The `r` samples are the values
`c (σ 0), …, c (σ (r−1))` for a uniformly random permutation `σ` of `Fin R`. -/
theorem bernstein_without_replacement {R : ℕ} (hR : 0 < R) (c : Fin R → ℝ) (r : ℕ)
    (hr : r ≤ R) (t : ℝ) (ht : 0 < t) :
    let cbar : ℝ := (∑ j : Fin R, c j) / (R : ℝ)
    let σR2 : ℝ := (∑ j : Fin R, (c j - cbar) ^ 2) / (R : ℝ)
    let ΔR : ℝ := (⨆ j : Fin R, c j) - (⨅ j : Fin R, c j)
    probPerm (fun σ : Equiv.Perm (Fin R) =>
        t ≤ |∑ k ∈ firstTimes R r, c (σ k) - (r : ℝ) * cbar|) ≤
      2 * Real.exp (-(t ^ 2) / (2 * (r : ℝ) * σR2 + t * ΔR)) := by sorry

end DynamicOnlineLP.DLA
