-- Prove2me | Theorems.Thm_AlgoPFR_lemma_5_1_extraction
-- name    : AlgoPFR.lemma_5_1_extraction
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:43:06.264658+00:00
-- url     : https://prove2.me/theorems/a2280d65-e4cd-4d7c-8a1d-7630c65ce530
-- title:
--   Lemma 5.1 — terminal subspace extraction with $O(n\log n)$ calls and $O(n^3)$ work
-- statement:
--   Let $C\ge0$ be a known absolute constant. There are a program and constants $C_1,C_2$ such that the following holds for every $n$ and every law $p$ on $\mathbb F_2^n$ with an envelope $M\ge\|p\|_\infty$ and $d[X;X]+\Delta[X]\le C$. Given $n$, a sample stream from $p$ and the density coin of rate $p/M$:
--
--   1. on every tape the program halts after at most $C_2(n+2)\log(n+2)$ samples and queries and log-cost time at most $C_2(n+2)^3$;
--   2. with probability at least $0.99$ it outputs a basis of a subspace $V\le\mathbb F_2^n$ with $d[X;U_V]\le C_1$.
--
--   Algorithm 3 of the source draws self-sums and retains those whose coin acceptance is high.
--
--   Differences from the source:
--
--   - encoding: algorithmic access to X → the sample stream and the density-coin oracle of the machine; reason: the machine form of Sample_X and Coin_X
--   - reading: O(n³) additional work, excluding the time spent in calls → the machine's whole log-cost time is at most C₂(n + 2)³; reason: each oracle instruction costs O(n + log n), and there are O(n log n) of them, so calls add O(n² log n) ≤ O(n³)
--   - encoding: O(n log n) calls → C₂ (n + 2) log(n + 2); reason: so that the bound stays meaningful at n = 0, 1
-- source:
--   Arunachalam, Dutt, Grewal, Gupte, Marton's conjecture in polynomial time, arXiv:2609.20771 (sha256 60e45066…), Lemma 5.1, p.41

import Mathlib
import Definitions.Def_AlgoPFR_Machine

set_option autoImplicit false

open scoped ENNReal Pointwise

namespace AlgoPFR

/-- **Lemma 5.1 (terminal subspace extraction, Algorithm 3).** Arunachalam, Dutt, Grewal, Gupte, *Marton's conjecture in polynomial time*, arXiv:2609.20771 (sha256 60e45066…), p.41: for a known absolute constant
`C ≥ 0` and algorithmic access to `X` with `d[X;X] + Δ[X] ≤ C`, an algorithm outputs with probability at
least `0.99` a basis of a subspace `V` with `d[X;U_V] = O(1)`; it makes `O(n log n)` calls to `Sample_X`,
`Coin_X` and performs `O(n³)` additional work.

**Formalization Note.** Access to `X` is the pair of machine oracles: the sample stream with law `p` and
the density coin with rate `p / M`. The program may depend on `C`, as in the paper, and receives only
`n`. The bounds hold on every tape. The cost bound is on the machine's whole log-cost time, including
the cost of its oracle instructions; each of those costs `O(n + log n)`, so with `O(n log n)` calls this
is the paper's `O(n³)` additional work. `n log n` is written `(n + 2) log (n + 2)` so as to stay
meaningful at `n = 0, 1`. -/
theorem lemma_5_1_extraction (C : ℝ) (hC : 0 ≤ C) :
    ∃ (P : Program) (C₁ C₂ : ℝ), ∀ (n : ℕ) (p : PMF (Vec n)) (M : ℝ),
      (∀ x, (p x).toReal ≤ M) → rd p p + (entropy p + Real.logb 2 M) ≤ C →
      (∀ ω : Tape n, ∃ t, (run n P (fun x => (p x).toReal / M) [n] ω t).out.isSome ∧
        (((run n P (fun x => (p x).toReal / M) [n] ω t).samples +
            (run n P (fun x => (p x).toReal / M) [n] ω t).queries : ℕ) : ℝ) ≤
          C₂ * ((n + 2) * Real.logb 2 (n + 2)) ∧
        ((run n P (fun x => (p x).toReal / M) [n] ω t).cost : ℝ) ≤ C₂ * (n + 2) ^ 3) ∧
      ProbAtLeast (tapeMeasure p)
        {ω | ∃ L : List (Vec n), Outputs n P (fun x => (p x).toReal / M) [n] ω (L.map encodeVec) ∧
          IsBasisList L ∧ rd p (subspaceLaw (listSpan L)) ≤ C₁} 0.99 := by sorry

end AlgoPFR
