-- Prove2me | Theorems.Thm_CSSNearGV_Amplification_low_weight_tails
-- name    : CSSNearGV.Amplification.low_weight_tails
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T21:18:32.467657+00:00
-- url     : https://prove2.me/theorems/cc33342d-0b92-4e38-a8fc-e79d0788d696
-- title:
--   Theorem 5.1 — expected low-weight counts and distance tails
-- statement:
--   Fix even $s\ge2$ and $\varepsilon>0$. The expected number of nonzero words of weight at most $(\delta^{(m)}-\varepsilon)n$ is
--   $$\widetilde O(n^{1-m})\quad\text{for DA, }m\ge2,\qquad
--   \widetilde O(n^{2-m})\quad\text{for AD, }m\ge3.$$
--   The probability of failing to have relative distance strictly greater than $\delta^{(m)}-\varepsilon$ has the same respective bounds. Both expected counts and both probability conclusions are asserted.
--
--   This combines the middle and boundary contributions.
--
--   Differences from the source:
--   - encoding: binary words, finite expectations and feasible entropy maxima → Fin-indexed binary vectors, exact finite averages and domain-restricted extrema; reason: the representation preserves the source objects and domains; endpoint values use continuous entropy extensions
--   - encoding: poly(n), soft-O and negligible estimates → eventual inequalities with positive constants, exponents and thresholds fixed before length and all weights; reason: the source leaves numerical prefactors unspecified; parameters s, m and epsilon are fixed before these constants
--   - reading: expected low-weight codewords in Theorem 5.1 → nonzero codewords only; reason: the explicit convention on printed p.9 / PDF 11 excludes the zero word, which otherwise contributes one at every round
-- source:
--   Rachel Yun Zhang, Linear-Time Encodable Quantum Codes near the CSS GV Bound, STOC 2027 submission #1164 (October 2026), Theorem 5.1, printed p.15 / PDF 17; nonzero convention printed p.9 / PDF 11

import Definitions.Def_CSSNearGV_Amplification_Estimates

open scoped BigOperators
noncomputable section

namespace CSSNearGV.Amplification

theorem low_weight_tails (s : ℕ) (hs : 2 ≤ s) (he : Even s) (ε : ℝ) (hε : 0 < ε) :
  (∀ m : ℕ, 2 ≤ m → DistanceTail s m false ε (1 - (m : ℝ))) ∧
  (∀ m : ℕ, 3 ≤ m → DistanceTail s m true ε (2 - (m : ℝ))) := by sorry

end CSSNearGV.Amplification
