-- Prove2me | Theorems.Thm_CorreaThreshold_Tight_bound_K0
-- name    : CorreaThreshold.Tight.bound_K0
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T12:37:12.287091+00:00
-- url     : https://prove2.me/theorems/207890fe-104a-4546-9ac2-2ca5c74f632c
-- title:
--   Appendix B — bound on the no-high-value contribution
-- statement:
--   Fix $n\ge2$ and $0\le k\le n^2$. Let $K$ count coordinates equal to the exceptional prize $H_n$, and let $R_n(X,\tau^{(k)})$ be the random-order reward of the two-level rule. The contribution from samples with no exceptional prize satisfies
--
--   $$
--   \mathbb E\big[R_n(X,\tau^{(k)});K=0\big]\le1-e^{-k/n}.
--   $$
--
--   This is the first term in the Appendix B decomposition by $K$.
--
--   **Formalization Note** The semicolon denotes an expectation restricted to the event, avoiding division by $\Pr(K=0)$. The paper's displayed intermediate inequality $1-(1-1/n)^k\le1-e^{-k/n}$ has the sign reversed, but the final bound is valid for this law.
-- source:
--   Correa, Foncea, Hoeksma, Oosterwijk, Vredeveld, Posted price mechanisms and optimal threshold strategies for random arrivals, Math. Oper. Res. 46 (2021), https://doi.org/10.1287/moor.2020.1105, p. 1474, Appendix B, first term

import Mathlib
import Definitions.Def_CorreaThreshold_Tight_Setting

namespace CorreaThreshold.Tight

open MeasureTheory

theorem bound_K0 (n : ℕ) (hn : 2 ≤ n) (k : ℕ) (hk : k ≤ n ^ 2) :
    (∫⁻ x in {x | Kcount n x = 0}, ENNReal.ofReal (ratioS (kRule n k) x)
      ∂(SamuelCahnProphet.IID.iidLaw (lawN n) (n ^ 2))) ≤
      ENNReal.ofReal (1 - Real.exp (-(k : ℝ) / n)) := by sorry

end CorreaThreshold.Tight
