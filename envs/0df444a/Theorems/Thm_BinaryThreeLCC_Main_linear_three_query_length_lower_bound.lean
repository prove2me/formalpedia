-- Prove2me | Theorems.Thm_BinaryThreeLCC_Main_linear_three_query_length_lower_bound
-- name    : BinaryThreeLCC.Main.linear_three_query_length_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:03:02.002922+00:00
-- url     : https://prove2.me/theorems/369baf5b-0985-4422-9dc5-4423c6f50fd4
-- title:
--   Theorem 1 — exponential square-root lower bound for binary linear 3-query LCCs
-- statement:
--   Let $C:\mathbb F_2^k\to\mathbb F_2^n$ be an injective linear code, with $n\ge1$. For each requested coordinate, let its randomized adaptive corrector read at most three oracle coordinates. Suppose that, for every message and every received word at Hamming distance at most $\delta n$ from its encoding, the corrector returns the requested encoded bit with probability at least $1-\varepsilon$, where $0<\delta<1$ and $0\le\varepsilon<1/2$. Then
--
--   $$k\le 2^{90}\delta^{-14}\bigl(\log_2(2n)\bigr)^2,\qquad
--   2n\ge 2^{2^{-45}\delta^7\sqrt{k}}.$$
--
--   In addition, for $n\ge2$,
--
--   $$n\ge 2^{2^{-46}\delta^7\sqrt{k}}.$$
--
--   The constants are absolute and uniform in every source parameter, including error probabilities arbitrarily close to $1/2$. This is the full operational-code conclusion, and gives the source's $n\ge2^{\Omega(\delta^7\sqrt{k})}$ rate.
--
--   **Formalization Note** The corrector is an arbitrary probability mass function on all depth-at-most-three binary oracle trees, with early stopping, adaptivity and repeated queries allowed. The encoding rows and combinatorial recovery matchings are not hypotheses.
--
--   Differences from the source:
--   - encoding: finite sets with one-based indices → finite types and zero-based Fin indices; reason: a change of enumeration preserves every vertex, coordinate and edge copy
--   - encoding: the asymptotic bound n ≥ 2^{Ω(δ⁷√k)} → the all-size rank bound with 2^90 and shifted exponential constant 2^(-45), plus the unshifted constant 2^(-46) for n ≥ 2; reason: printed pp.10–18 give uniform proof constants; n=k=1 with the identity code and δ=1/4 excludes an unshifted positive exponent at n=1
-- source:
--   Oliver Janzer, Peter Manohar, STOC 2027 submission #732 (October 2026), Theorem 1, printed p. 2, PDF p. 4; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/732.pdf

import Definitions.Def_BinaryThreeLCC_Main_Matchings

set_option autoImplicit false

namespace BinaryThreeLCC.Main

/-- Theorem 1, with absolute constants, all positive lengths, and the unshifted
exponential consequence on n ≥ 2. No condition on ε beyond the printed range. -/
theorem linear_three_query_length_lower_bound {k n : ℕ} (hn : 0 < n)
    (C : CodeModel k n) (δ ε : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hε : 0 ≤ ε) (hε1 : ε < 1 / 2) (hcorrect : Corrects C δ ε) :
    (k : ℝ) ≤ (2 : ℝ) ^ 90 * δ ^ (-14 : ℤ) * (Real.logb 2 (2 * (n : ℝ))) ^ 2 ∧
    (2 : ℝ) ^ ((2 : ℝ) ^ (-45 : ℤ) * δ ^ 7 * Real.sqrt k) ≤ 2 * (n : ℝ) ∧
    (2 ≤ n → (2 : ℝ) ^ ((2 : ℝ) ^ (-46 : ℤ) * δ ^ 7 * Real.sqrt k) ≤ (n : ℝ)) := by sorry

end BinaryThreeLCC.Main
