-- Prove2me | Theorems.Thm_BipHamCount_Deterministic_base_comparison
-- name    : BipHamCount.Deterministic.base_comparison
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:47:44.524686+00:00
-- url     : https://prove2.me/theorems/9b3fa2ac-72ad-4146-b591-188fdfcb3be3
-- title:
--   §4 base comparison — both exact bases are below 1.9526
-- statement:
--   For the exact rational $\alpha=60909/100000$ and binary entropy $h$ in nats,
--   $$\exp(h(\alpha))<\frac{19526}{10000},\qquad \exp(h(\alpha)/2)3^{\alpha/2}<\frac{19526}{10000}.$$
--   Both strict inequalities are asserted with the paper's decimal constants, without rounding either base. Their strict margins allow the polynomial factors in the program bounds to be absorbed in the goal's exponential bound.
--
--   Differences from the source:
--   - encoding: binary entropy H in base two → Real.binEntropy in nats with exp replacing 2 raised to H; reason: exp(m·binEntropy x)=2^(m·H(x)), including x=0,1
-- source:
--   Koana, Kumabe, Counting Hamiltonian Cycles in Bipartite Digraphs Deterministically in O(1.9526^n) Time, STOC 2027 submission #814 (October 2026), §4 base comparison, p. 6. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/814.pdf

import Mathlib
import Definitions.Def_BipHamCount_Deterministic_Core

open scoped BigOperators

namespace BipHamCount.Deterministic

/-- §4 base comparison p.6 (also p.4); the exact α=60909/100000 and base 1.9526. -/
theorem base_comparison :
    Real.exp (Real.binEntropy alpha) < (19526/10000 : ℝ) ∧
      Real.exp (Real.binEntropy alpha / 2) * (3 : ℝ)^(alpha/2) <
        (19526/10000 : ℝ) := by sorry

end BipHamCount.Deterministic
