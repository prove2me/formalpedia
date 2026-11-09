-- Prove2me | Theorems.Thm_BipHamCount_Deterministic_binomial_entropy
-- name    : BipHamCount.Deterministic.binomial_entropy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:47:45.130004+00:00
-- url     : https://prove2.me/theorems/71eec4d0-feb2-4cb1-9543-077b2341e017
-- title:
--   §2 binomial bound — every coefficient is bounded by entropy
-- statement:
--   For every pair of natural numbers $m,q$ with $q\le m$, write $h(x)=-x\ln x-(1-x)\ln(1-x)$, with $h(0)=h(1)=0$. Then
--   $$\binom mq\le\exp\big(mh(q/m)\big).$$
--   At $m=q=0$, the quotient is interpreted as zero and both sides equal one. The bound covers the entire range, including $q>m/2$. The published choose_sum_le_exp_mul_binEntropy bounds a partial sum only when $2q\le m$, so it does not replace this statement. This estimate controls subset layers in the running-time analysis.
--
--   Differences from the source:
--   - encoding: binary entropy H in base two → Real.binEntropy in nats with exp replacing 2 raised to H; reason: exp(m·binEntropy x)=2^(m·H(x)), including x=0,1
--   - encoding: m=n/2 is a side size → an arbitrary natural side size m, including zero; reason: every balanced bipartite input has this size; at m=q=0 both sides are one under the stated total-division convention
-- source:
--   Koana, Kumabe, Counting Hamiltonian Cycles in Bipartite Digraphs Deterministically in O(1.9526^n) Time, STOC 2027 submission #814 (October 2026), §2 binomial bound, p. 5. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/814.pdf

import Mathlib
import Definitions.Def_BipHamCount_Deterministic_Core

open scoped BigOperators

namespace BipHamCount.Deterministic

/-- §2 binomial bound, p.5, for the entire range q≤m. Entropy is in nats.
For m=q=0 the quotient is 0 and both sides are 1. -/
theorem binomial_entropy (m q : ℕ) (hq : q ≤ m) :
    (m.choose q : ℝ) ≤ Real.exp ((m : ℝ) * Real.binEntropy ((q : ℝ) / m)) := by sorry

end BipHamCount.Deterministic
