-- Prove2me | Theorems.Thm_CorreaThreshold_Tight_kRule_value_le
-- name    : CorreaThreshold.Tight.kRule_value_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T12:37:44.603982+00:00
-- url     : https://prove2.me/theorems/2541e037-e508-4036-b6e9-010eb2b1cf07
-- title:
--   Appendix B — uniform asymptotic reward bound for two-level rules
-- statement:
--   For every $\varepsilon>0$, there is $N$ such that, for each $n\ge N$ and each $0\le k\le n^2$, the canonical two-level rule obeys
--
--   $$
--   V_n(\tau^{(k)})\le
--   (1-e^{-1})\frac{e-1}{e-2}+\varepsilon.
--   $$
--
--   The bound is uniform in the choice of $k$ and is the final estimate in Appendix B. It combines with the reduction to two-level rules and the prophet's limit to establish tightness for every nonadaptive threshold rule.
--
--   **Formalization Note** The statement includes $k=0$, when only exceptional prizes are accepted; Appendix B's intermediate $1/k$ estimate concerns $k\ge1$, but the final bound also covers $k=0$. Expectations are in $[0,\infty]$.
-- source:
--   Correa, Foncea, Hoeksma, Oosterwijk, Vredeveld, Posted price mechanisms and optimal threshold strategies for random arrivals, Math. Oper. Res. 46 (2021), https://doi.org/10.1287/moor.2020.1105, p. 1474, Appendix B, final display

import Mathlib
import Definitions.Def_CorreaThreshold_Tight_Setting

namespace CorreaThreshold.Tight

open MeasureTheory

theorem kRule_value_le :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ k : ℕ, k ≤ n ^ 2 →
        value n (kRule n k) ≤
          ENNReal.ofReal ((1 - Real.exp (-1)) *
            ((Real.exp 1 - 1) / (Real.exp 1 - 2)) + ε) := by sorry

end CorreaThreshold.Tight
