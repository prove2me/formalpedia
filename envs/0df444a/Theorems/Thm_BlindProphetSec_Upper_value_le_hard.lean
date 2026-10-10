-- Prove2me | Theorems.Thm_BlindProphetSec_Upper_value_le_hard
-- name    : BlindProphetSec.Upper.value_le_hard
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T23:32:26.887987+00:00
-- url     : https://prove2.me/theorems/ae109a1d-e6bc-4e82-9a2e-58d5afc789da
-- title:
--   §5, p. 19, third display — on the §5 instance every stopping strategy earns at most 1 + a²/2 + O(1/n)
-- statement:
--   Fix $a\in[0,1]$. There is a constant $C$ (depending on $a$ only) such that for every $n\ge1$ and every stopping strategy of the gambler on the §5 instance with $n+1$ variables ($V_1,\dots,V_n$ equal $n$ with probability $1/n^2$ and $0$ otherwise, $V_{n+1}\equiv a$), arriving in uniformly random order,
--   $$\mathbb E(V_{\sigma_T}) \le 1 + \frac{a^2}{2} + \frac{C}{n}.$$
--   Here a strategy may observe the identities and values seen so far, may randomize, and may depend on the instance.
--
--   This bound, together with $\mathbb E(\max_i V_i)\to 1+a$, yields $\limsup_n \mathbb E(V_{\sigma_T})/\mathbb E(\max_i V_i)\le (1+a^2/2)/(1+a)$, which equals $\sqrt3-1$ at $a=\sqrt3-1$.
--
--   **Formalization Note** The paper's $O(1/n)$ is written out as its definition, $\exists C\ \forall n\ge1$, with $C$ chosen after $a$ and before $n$ and the strategy. The statement quantifies over all strategies of the class `Strategy (n+1)`, not only over time-$j$ rules: the reduction to time-$j$ rules ("solving the dynamic programming") is part of what is to be proved.
-- source:
--   Correa, Saona & Ziliotto, Prophet Secretary Through Blind Strategies, arXiv:1807.07483v2, p. 19, §5, third display (E(V_{σ_T}) = … ≤ 1 + a²/2 + O(1/n)) and the dynamic-programming sentence before the first display

import Mathlib
import Definitions.Def_BlindProphetSec_Upper_Setting

open MeasureTheory Filter Topology

namespace BlindProphetSec.Upper

theorem value_le_hard (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ s : Strategy (n + 1),
      value s (hardLaw n a) ≤ ENNReal.ofReal (1 + a ^ 2 / 2 + C / n) := by sorry

end BlindProphetSec.Upper
