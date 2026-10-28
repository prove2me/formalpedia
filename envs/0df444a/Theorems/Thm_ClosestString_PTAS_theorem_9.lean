-- Prove2me | Theorems.Thm_ClosestString_PTAS_theorem_9
-- name    : ClosestString.PTAS.theorem_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T16:19:13.33399+00:00
-- url     : https://prove2.me/theorems/7664e3eb-37de-4a3a-9284-1434b218919f
-- title:
--   Theorem 9 — Algorithm closestSubstring is a PTAS: cost ≤ (1 + 1/(2r−1) + 3εr)·d_opt with probability ≥ 1 − 2(nm)^{−1/3}, with polynomially many candidates
-- statement:
--   Fix a finite alphabet $\Sigma$, an integer $r\ge2$ and $\varepsilon>0$, and run Algorithm closestSubstring (Figure 3) with these constants.
--
--   1. **Approximation.** For every instance — strings $s_1,\dots,s_n$ ($n\ge1$) of length $m$ and an integer $1\le L\le m$ — and every solver of problem (8) that returns a solution within error $\varepsilon|P|$ (Figure 3, step 1(c)(ii)), with probability at least $1-2(nm)^{-1/3}$ over the random multisets of step 1(b) the output $s'$ satisfies
--   $$\max_{1\le i\le n}\ \min_{t_i\sqsubseteq s_i}d(s',t_i)\ \le\ \Big(1+\frac1{2r-1}+3\varepsilon r\Big)d_{\mathrm{opt}},$$
--   where $d_{\mathrm{opt}}$ is the optimal Closest Substring radius.
--   2. **Polynomial size.** There is a constant $c$, depending only on $|\Sigma|$, $r$ and $\varepsilon$, such that for every instance the number of candidates the algorithm evaluates (one call of the solver for each candidate of step 1, plus the substrings of $s_1$ in step 2) is at most $c\,(nm+1)^c$.
--
--   Choosing $r$ and $\varepsilon$ with $\frac1{2r-1}+3\varepsilon r\le\delta$ gives, for every $\delta>0$, a $(1+\delta)$-approximation with high probability using polynomially many solver calls: Algorithm closestSubstring is a polynomial-time approximation scheme for Closest Substring, relative to a solver of (8). The paper remarks that the algorithm can be derandomized by standard methods; that remark is not part of this statement.
--
--   Differences from the source:
--
--   - reading: "is a PTAS" (proof: "with high probability … no more than (1 + δ)d_opt", "runs in polynomial time for any fixed positive r and ε") → (a) cost ≤ (1 + 1/(2r−1) + 3εr)·d_opt with probability ≥ 1 − 2(nm)^{−1/3}; (b) ∃ c depending on |Σ|, r, ε with #candidates ≤ c(nm + 1)^c; reason: the explicit factor and probability are the ones the proof derives (pp. 11–12); Lean has no machine model, so polynomial time is the polynomial number of candidates and solver calls, the solver's own running time (LP plus derandomized rounding, Lemma 6) being outside the statement
--   - generalization: step 1(c)(ii) solves (8) "using the method provided in the proof of Lemma 6 … within error ε|P|" → every solver that sees only the instance (t′, P, offsets) of (8) and returns x with d(t′_i|P, x) + offset_i ≤ d0 + ε|P| for all i (IsApproxSolver); reason: the proof uses only this guarantee; the method of Lemma 6 (and the exact minimizer of (8)) satisfies it
--   - reading: log(nm) → Real.log, the natural logarithm; reason: (11) needs exp(−ε²|R|/2) ≤ (nm)^{−2}, i.e. |R| ≥ (4/ε²) ln(nm), which is exactly the printed computation with ln
--   - encoding: t′_i "a length L substring of si minimizing …"; "Output the s′ with minimum c" → ties in step 1(c)(i) go to the smallest start position; the output is a cost minimizer chosen by Classical.choose; reason: the paper leaves the choice open; every minimizer has the same output cost, and the proof works for every minimizer in step 1(c)(i)
--   - encoding: R a multiset of uniformly random positions from P, for each tuple → algLaw: independent samples across tuples, each a product of k uniform laws on P_τ; the Dirac mass at the constant multiset 0 when P_τ = ∅; reason: when P_τ = ∅ the sample is never read; same algorithm
--   - encoding: an instance ⟨S, L⟩ with S ⊆ Σ^m → n ≥ 1 strings S : Fin n → Fin m → A, 1 ≤ L ≤ m, 0-based positions, substrings by start position; reason: step 2 needs s_1 and Figure 3 needs a length-L substring of every s_i; the empty-string case L = 0 is excluded
--   - encoding: step 1's tuples "allowing repeats, but if t_ij and t_ik are both chosen from the same s_i then t_ij = t_ik" (equal as strings) → admissible tuples of (string index, start position) in which two entries from the same s_i have the same start position; reason: a tuple of the paper whose same-string entries are equal strings at different starts has the same substrings, hence the same Q, P, t_{i1} and the same step-1 candidates, as the tuple with those entries at one start; the candidate set of step 3 is unchanged
-- source:
--   Li, Ma & Wang, On the Closest String and Substring Problems, arXiv:cs/0002012v1, p. 9, Theorem 9 (Algorithm closestSubstring, Figure 3, p. 10; proof pp. 9–12, constants on pp. 11–12)

import Mathlib
import Definitions.Def_ClosestString_PTAS_Algorithm

namespace ClosestString.PTAS

/-- **Theorem 9** (Li, Ma & Wang, arXiv:cs/0002012v1, p. 9; proof pp. 9–12): Algorithm
closestSubstring (Figure 3) is a PTAS for Closest Substring. Fix the alphabet `A`, an integer
`r ≥ 2` and `ε > 0`.
(a) For every instance (`n ≥ 1` strings of length `m`, `1 ≤ L ≤ m`) and every solver of problem (8)
within error `ε|P|`, with probability at least `1 − 2(nm)^{−1/3}` over the random multisets, the
output's cost is at most `(1 + 1/(2r−1) + 3εr) d_opt`.
(b) The number of candidates the algorithm evaluates (one solver call per step-1 candidate) is
bounded by a polynomial `c (nm + 1)^c` in the input size, `c` depending only on `|A|`, `r`, `ε`. -/
theorem theorem_9 {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A] (r : ℕ) [NeZero r]
    (hr : 2 ≤ r) (ε : ℝ) (hε : 0 < ε) :
    (∀ (n m L : ℕ) [NeZero n] [NeZero L] (hL : L ≤ m) (S : Fin n → Fin m → A)
        (solver : Solver A n L), IsApproxSolver ε solver →
        ENNReal.ofReal (1 - 2 * ((n : ℝ) * m) ^ (-(1 / 3 : ℝ))) ≤
          algLaw S r ε {ω | (cost S (closestSubstring S hL r ε solver ω) : ℝ)
            ≤ (1 + 1 / (2 * (r : ℝ) - 1) + 3 * ε * r) * dOpt L S}) ∧
    (∃ c : ℕ, ∀ (n m L : ℕ), 1 ≤ n → 1 ≤ L → L ≤ m →
        Fintype.card (Cand A n m L r (sampleSize n m ε)) ≤ c * (n * m + 1) ^ c) := by sorry

end ClosestString.PTAS
