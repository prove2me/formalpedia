-- Prove2me | Theorems.Thm_AlgoPFR_theorem_1_2_algorithmic_pfr
-- name    : AlgoPFR.theorem_1_2_algorithmic_pfr
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:43:01.555458+00:00
-- url     : https://prove2.me/theorems/7dcc39e9-bf71-4568-beb9-6b971cc02366
-- title:
--   Theorem 1.2 (Algorithmic PFR) — a PFR subspace of $A$ from samples and membership queries in $\mathrm{poly}(n,K,\log(1/\delta))$
-- statement:
--   There is one randomized program, with constants $C,c,C',c'$, such that the following holds for every $n$, every nonempty $A\subseteq\mathbb F_2^n$ and all real $K$ and $\delta$ with $|A+A|\le K|A|$ and $0<\delta<1$. Given uniform samples from $A$ and a membership oracle for $A$:
--
--   1. with probability at least $1-\delta$ the program outputs a basis of a subspace $V\le\mathbb F_2^n$ with $|V|\le|A|$ such that $A$ is covered by at most $CK^c$ translates of $V$;
--   2. on every run it halts within
--   $$C'\bigl(n+K+\log(1/\delta)+2\bigr)^{c'}$$
--   time, samples and membership queries.
--
--   This is the main result of the source. It turns the existential polynomial Freiman–Ruzsa theorem into an algorithm with polynomial dependence on both $n$ and $K$; earlier algorithms took time $\mathrm{poly}(n,2^K)$.
--
--   **Formalization Note** Time is log-cost time on the machine of `AlgoPFR.Machine`. A run is a tape whose samples lie in $A$. The program receives only $n$, $\lceil K\rceil$ and $\lceil\log_2(1/\delta)\rceil$.
--
--   Differences from the source:
--
--   - generalization: the algorithm knows K and δ → the program receives only ⌈K⌉ and ⌈log₂(1/δ)⌉; reason: less input information, so a stronger existence claim that gives the printed one; K stays real in the hypothesis and the bounds
--   - generalization: uses poly(n, K, log(1/δ)) time, samples, and membership queries → the bound holds on every run, not in expectation; reason: the stronger reading: the budgets of Algorithm 2 and §6 make every run bounded
--   - encoding: K^O(1) and poly(n, K, log(1/δ)) → C · K^c and C′(n + K + log₂(1/δ) + 2)^c′, with constants before n, A, K, δ; reason: one program for all inputs, with + 2 so the bound is positive at n = 0, K = 1, δ near 1
--   - encoding: a randomized algorithm and "time" → a program of the randomized log-cost oracle RAM; reason: the source names no model; bit lengths are charged, so polynomial time is the Turing-machine class
--   - encoding: with probability at least 1 − δ → the success event contains a measurable event of measure ≥ 1 − δ; reason: inner measure, which needs no measurability proof and is not weakened by an outer measure
--   - encoding: a basis for a subspace V → a linearly independent list L, with V = span L; reason: the same object, in the output encoding
-- source:
--   Arunachalam, Dutt, Grewal, Gupte, Marton's conjecture in polynomial time, arXiv:2609.20771 (sha256 60e45066…), Theorem 1.2, p.2

import Mathlib
import Definitions.Def_AlgoPFR_Machine

set_option autoImplicit false

open scoped ENNReal Pointwise

namespace AlgoPFR

/-- **Theorem 1.2 (Algorithmic PFR).** Arunachalam, Dutt, Grewal, Gupte, *Marton's conjecture in polynomial time*, arXiv:2609.20771 (sha256 60e45066…), p.2: let `0 < δ < 1` and let `A ⊆ F₂ⁿ` be nonempty with
`|A + A| ≤ K|A|`. Given uniform sampling and membership-oracle access to `A`, there is a randomized
algorithm that, with probability at least `1 − δ`, outputs a basis for a subspace `V ≤ F₂ⁿ` with `|V| ≤ |A|`
such that `A` can be covered by at most `K^O(1)` translates of `V`. It uses `poly(n, K, log(1/δ))` time,
samples, and membership queries.

**Formalization Note.** One program and the constants `C, c, C′, c′` come before `n, A, K, δ`. The machine is
the log-cost oracle RAM of `Instr`; the program sees only `n`, `⌈K⌉`, `⌈log₂(1/δ)⌉` and the two oracles for
`A`. The resource bound holds on every run, that is on every tape whose samples lie in `A`, not merely in
expectation. -/
theorem theorem_1_2_algorithmic_pfr :
    ∃ (P : Program) (C C' : ℝ) (c c' : ℕ), ∀ (n : ℕ) (A : Finset (Vec n)) (hA : A.Nonempty) (K δ : ℝ),
      ((A + A).card : ℝ) ≤ K * A.card → 0 < δ → δ < 1 →
      (∀ ω : Tape n, IsRunTape A ω →
        HaltsWithin n P (memberRate A) [n, ⌈K⌉₊, ⌈Real.logb 2 (1 / δ)⌉₊] ω
          (C' * ((n : ℝ) + K + Real.logb 2 (1 / δ) + 2) ^ c')) ∧
      ProbAtLeast (tapeMeasure (uniformLaw A hA))
        {ω | ∃ o, Outputs n P (memberRate A) [n, ⌈K⌉₊, ⌈Real.logb 2 (1 / δ)⌉₊] ω o ∧
          IsPFROutput A K C c o} (1 - δ) := by sorry

end AlgoPFR
