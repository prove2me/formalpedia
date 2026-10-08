-- Prove2me | Theorems.Thm_CorreaThreshold_Tight_bound_K1
-- name    : CorreaThreshold.Tight.bound_K1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T12:37:24.027981+00:00
-- url     : https://prove2.me/theorems/871cf4ac-6c94-49db-a533-d3c5022782ee
-- title:
--   Appendix B — valid bound on the one-high-value contribution
-- statement:
--   Fix $n\ge2$ and $1\le k\le n^2$. For the same two-level rule and high-value count $K$, the one-high-value contribution satisfies
--
--   $$
--   \mathbb E\big[R_n(X,\tau^{(k)});K=1\big]\le
--   \frac1n\left(1+\frac{n^2}{(e-2)k}(1-e^{-k/n})\right).
--   $$
--
--   This is the penultimate upper bound in Appendix B's displayed chain, and its $1/n$ term disappears in the asymptotic limit.
--
--   **Formalization Note** The printed final line drops the positive $1/n$ term and is false for finite $n$; this theorem retains it. The lower bound $k\ge1$ gives meaning to the paper's $1/k$. The semicolon denotes an event-restricted expectation.
-- source:
--   Correa, Foncea, Hoeksma, Oosterwijk, Vredeveld, Posted price mechanisms and optimal threshold strategies for random arrivals, Math. Oper. Res. 46 (2021), https://doi.org/10.1287/moor.2020.1105, p. 1474, Appendix B, second term, penultimate line

import Mathlib
import Definitions.Def_CorreaThreshold_Tight_Setting

namespace CorreaThreshold.Tight

open MeasureTheory

theorem bound_K1 (n : ℕ) (hn : 2 ≤ n) (k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ n ^ 2) :
    (∫⁻ x in {x | Kcount n x = 1}, ENNReal.ofReal (ratioS (kRule n k) x)
      ∂(SamuelCahnProphet.IID.iidLaw (lawN n) (n ^ 2))) ≤
      ENNReal.ofReal ((1 / (n : ℝ)) *
        (1 + (n : ℝ) ^ 2 / ((Real.exp 1 - 2) * k) *
          (1 - Real.exp (-(k : ℝ) / n)))) := by sorry

end CorreaThreshold.Tight
