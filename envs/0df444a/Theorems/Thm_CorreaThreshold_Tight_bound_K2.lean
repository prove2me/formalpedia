-- Prove2me | Theorems.Thm_CorreaThreshold_Tight_bound_K2
-- name    : CorreaThreshold.Tight.bound_K2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T12:37:35.083224+00:00
-- url     : https://prove2.me/theorems/adde88a6-20c7-4ccf-8ab6-a87f515f23db
-- title:
--   Appendix B — bound on the multiple-high-value contribution
-- statement:
--   Fix $n\ge2$ and $0\le k\le n^2$. The contribution to the two-level rule's expected reward from samples with at least two exceptional prizes satisfies
--
--   $$
--   \mathbb E\big[R_n(X,\tau^{(k)});K\ge2\big]\le\frac1{n(e-2)}.
--   $$
--
--   This bounds the rare-event term of the Appendix B decomposition and vanishes as $n$ grows.
--
--   **Formalization Note** The expectation is restricted to $\{K\ge2\}$ rather than expressed as a conditional expectation times its probability.
-- source:
--   Correa, Foncea, Hoeksma, Oosterwijk, Vredeveld, Posted price mechanisms and optimal threshold strategies for random arrivals, Math. Oper. Res. 46 (2021), https://doi.org/10.1287/moor.2020.1105, p. 1474, Appendix B, third term

import Mathlib
import Definitions.Def_CorreaThreshold_Tight_Setting

namespace CorreaThreshold.Tight

open MeasureTheory

theorem bound_K2 (n : ℕ) (hn : 2 ≤ n) (k : ℕ) (hk : k ≤ n ^ 2) :
    (∫⁻ x in {x | 2 ≤ Kcount n x}, ENNReal.ofReal (ratioS (kRule n k) x)
      ∂(SamuelCahnProphet.IID.iidLaw (lawN n) (n ^ 2))) ≤
      ENNReal.ofReal (1 / ((n : ℝ) * (Real.exp 1 - 2))) := by sorry

end CorreaThreshold.Tight
