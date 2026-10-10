-- Prove2me | Theorems.Thm_BlindProphetSec_Upper_expected_max_hard
-- name    : BlindProphetSec.Upper.expected_max_hard
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T23:32:08.865003+00:00
-- url     : https://prove2.me/theorems/4d61cc6a-2c08-4016-988e-a33ed64ebaed
-- title:
--   §5, p. 19, fourth display — E(max) of the §5 instance is n[1 − (1 − 1/n²)ⁿ] + (1 − 1/n²)ⁿ a, which tends to 1 + a
-- statement:
--   Fix $a\in[0,1]$. For $n\ge1$ consider the $n+1$ independent variables of §5: $V_1,\dots,V_n$ take the value $n$ with probability $1/n^2$ and $0$ otherwise, and $V_{n+1}\equiv a$. Then the prophet's expected value is
--   $$\mathbb E\Big(\max_{1\le i\le n+1} V_i\Big) = n\Big[1-\Big(1-\frac1{n^2}\Big)^n\Big] + \Big(1-\frac1{n^2}\Big)^n a,$$
--   and this quantity tends to $1+a$ as $n\to\infty$.
--
--   This is the denominator of the ratio whose limit superior gives the bound $\sqrt3-1$ of Theorem 1.3.
--
--   **Formalization Note** The paper's display writes $\max_{i\in[n]}$, but its right-hand side contains $a$; the maximum is over all $n+1$ variables, and the Lean statement uses all of them. The limit is stated for the real numbers $\mathbb E(\max)$ (finite for every $n$), with the sequence indexed by all $n\in\mathbb N$.
-- source:
--   Correa, Saona & Ziliotto, Prophet Secretary Through Blind Strategies, arXiv:1807.07483v2, p. 19, §5, fourth display (E(max_{i∈[n]}{V_i}) = …)

import Mathlib
import Definitions.Def_BlindProphetSec_Upper_Setting

open MeasureTheory Filter Topology

namespace BlindProphetSec.Upper

theorem expected_max_hard (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (∀ n : ℕ, 1 ≤ n →
      BlindProphetSec.Blind.Emax (hardLaw n a) =
        ENNReal.ofReal ((n : ℝ) * (1 - (1 - 1 / (n : ℝ) ^ 2) ^ n) +
          (1 - 1 / (n : ℝ) ^ 2) ^ n * a)) ∧
    Tendsto (fun n : ℕ => (BlindProphetSec.Blind.Emax (hardLaw n a)).toReal) atTop (𝓝 (1 + a)) := by sorry

end BlindProphetSec.Upper
