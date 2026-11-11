-- Prove2me | Theorems.Thm_EqualSubsetSum_Faster_lemma_7_1
-- name    : EqualSubsetSum.Faster.lemma_7_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:24:16.201875+00:00
-- url     : https://prove2.me/theorems/93ae8e6e-e1d7-4b9c-b2af-fdd09257e40b
-- title:
--   Lemma 7.1 — the simpler procedures and their exponents on the remaining ranges of p
-- statement:
--   For each range of the zero fraction $p=k/n$ in the table there is a procedure, working for all input lengths, that returns only solutions for $x$, obeys a work limit on every input, and fails with probability $2^{-\Omega(n)}$ when the guess is correct; up to polynomial factors the cap is $2^{n\cdot\text{exponent}}$:
--
--   | zero fraction $p$ | exponent |
--   |---|---|
--   | $p<1/9$ or $p>3/5$ | $\tfrac12[H(p)+1-p]<.7$ |
--   | $1/3\le p\le 3/5$ | $\max\{1/2,1-p\}\le 2/3$ |
--   | $1/9\le p<1/3$ | $C(p)$ (step-two), $f(p)$ (fully compatible) |
--
--   Here $f(p)=H(p)+2(1-p)-\log_2 3$ and $C(p)=\min_{0\le q\le(1-p)/2}\max\{H(p)+q,(1-p)[1-H(q/(1-p))]\}$ is increasing on $[1/9,1/3]$. For $u=1-p$ and every $0\le q\le u/2$,
--   $$C(p)\le\max\Big\{H(p)+q,\ u[1-H(q/u)],\ \frac{H(p)+p+q+uH(q/u)}2,\ \frac12\Big\}.\tag{40}$$
--
--   In Lean: four guess procedures (`IsGuessProcedure`), the two inequalities of the table for real $p\in[0,1)$, `StrictMonoOn C [1/9, 1/3]`, and (40) as $C(p)\le T(p,q)$.
--
--   Differences from the source:
--   - reading: a randomized algorithm, its bit operations and its executions → a program of the published log-cost randomized RAM SubsetSumPartialMatch_SubsetSum_RAM, its charged cost, and each random tape; reason: the paper's cost model (§2.1: bit operations including arithmetic, memory addressing, sorting, random-bit generation) read as that machine
--   - encoding: procedures for each range of p, receiving x and a guess k → one program per row with input words n, k, x₁, …, xₙ, k : ℕ, n ≥ 1, k < n, k/n in the row; reason: guesses are k ∈ {0, …, n − 1} (§3)
--   - reading: obeys a computable work limit on every input; up to polynomial factors the cap is 2^{n·exponent} → on every tape the program halts within C(n + m + 1)^K·2^{n·E(k/n)}; reason: a cost bound on every tape; a computable cap follows, since cost bounds the coins read and the worst case over the finitely many coin prefixes can be simulated
--   - encoding: poly(n + m) (a fixed polynomial in n + m) → C·(n + m + 1)^K with constants C, K fixed before the input, m = maxBits x; reason: explicit form of the paper's O*-notation (§1.1)
--   - encoding: failure probability 2^{−Ω(n)} → probability of the output [0] at most C'·2^{−c n} with c > 0, C' fixed, for every n; reason: explicit form of Ω(n); a bound for all n is the same as one for large n up to the constant C'
--   - reading: the table's inequalities < .7 and ≤ 2/3 for the ranges of p → for every real p ∈ [0, 1) in the range (resp. every real p ∈ [1/3, 3/5]); reason: zero fractions lie in [0, 1); the real-interval reading contains all rational k/n
--   - reading: (40): for u = 1 − p and every 0 ≤ q ≤ u/2 → for every real p ∈ [0, 1) and every q ∈ [0, (1 − p)/2]; reason: the sentence leaves the range of p implicit; the wider reading is taken
--   - reading: C is increasing on [1/9, 1/3] → StrictMonoOn C (Icc (1/9) (1/3)); reason: strict reading, as in Lemma B.1
-- source:
--   Cheshm Jahan, Keshavarz Hedayati, Safari, Shahrezaei, Faster Equal-Subset-Sum via Truncated Inclusion–Exclusion, STOC 2027 submission (manuscript, sha256 7ad8c8b2…61dacd1), p. 44, Lemma 7.1

import Mathlib
import Definitions.Def_SubsetSumPartialMatch_SubsetSum_RAM
import Definitions.Def_EqualSubsetSum_Faster_Problem
import Definitions.Def_EqualSubsetSum_Faster_Exponents

namespace EqualSubsetSum.Faster

open SubsetSumPartialMatch.SubsetSum

/-- Lemma 7.1 (p. 44). For each row of the table there is a procedure, valid for all input
lengths, that returns only solutions for `x`, halts within `poly(n + m) 2^{n E(p)}` bit
operations on every tape, and fails with probability `2^{-Ω(n)}` for a correct guess:
`E(p) = [H(p) + 1 - p]/2` for `p < 1/9` or `p > 3/5`; `E(p) = max{1/2, 1 - p}` for
`1/3 ≤ p ≤ 3/5`; `E = C` (step-two) and `E = f` (fully compatible) for `1/9 ≤ p < 1/3`. Moreover
`[H(p) + 1 - p]/2 < .7` on the first range, `max{1/2, 1 - p} ≤ 2/3` on the second, `C` is
increasing on `[1/9, 1/3]`, and `C(p) ≤ T(p, q)` for every `0 ≤ q ≤ (1-p)/2` (eq. (40)). -/
theorem lemma_7_1 :
    (∃ P : Program, IsGuessProcedure P {p | p < 1 / 9 ∨ 3 / 5 < p} (fun p => (H p + 1 - p) / 2)) ∧
    (∃ P : Program, IsGuessProcedure P (Set.Icc (1 / 3) (3 / 5)) (fun p => max (1 / 2) (1 - p))) ∧
    (∃ P : Program, IsGuessProcedure P (Set.Ico (1 / 9) (1 / 3)) Cstep) ∧
    (∃ P : Program, IsGuessProcedure P (Set.Ico (1 / 9) (1 / 3)) fCompat) ∧
    (∀ p ∈ Set.Ico (0 : ℝ) 1, (p < 1 / 9 ∨ 3 / 5 < p) → (H p + 1 - p) / 2 < 7 / 10) ∧
    (∀ p ∈ Set.Icc (1 / 3 : ℝ) (3 / 5), max (1 / 2) (1 - p) ≤ 2 / 3) ∧
    StrictMonoOn Cstep (Set.Icc (1 / 9) (1 / 3)) ∧
    (∀ p ∈ Set.Ico (0 : ℝ) 1, ∀ q ∈ Set.Icc (0 : ℝ) ((1 - p) / 2), Cstep p ≤ Tstep p q) := by sorry

end EqualSubsetSum.Faster
