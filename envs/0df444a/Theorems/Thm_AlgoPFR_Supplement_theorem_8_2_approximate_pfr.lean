-- Prove2me | Theorems.Thm_AlgoPFR_Supplement_theorem_8_2_approximate_pfr
-- name    : AlgoPFR.Supplement.theorem_8_2_approximate_pfr
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T22:37:35.845556+00:00
-- url     : https://prove2.me/theorems/f01ef093-52e0-40a0-843a-b523aba458c6
-- title:
--   Theorem 8.2 — approximate algorithmic PFR from $R$-uniform samples in $\mathrm{poly}(n,K,R,\log(1/\delta))$ time
-- statement:
--   There are one randomized program and constants $C,c,C',c'$ such that the following holds for every $n$, every nonempty $A\subseteq\mathbb F_2^n$, all reals $K,R,\delta$ with $|A+A|\le K|A|$ and $0<\delta<1$, and every $R$-uniform distribution $\mu$ on $A$. Given independent samples from $\mu$ and a membership oracle for $A$:
--
--   1. with probability at least $1-\delta$ the program outputs a basis of a subspace $V\le\mathbb F_2^n$ with $|V|\le|A|$ such that $A$ is covered by at most $CK^c$ translates of $V$;
--   2. on every run it halts within
--   $$C'\bigl(n+K+R+\log(1/\delta)+2\bigr)^{c'}$$
--   time, samples and membership queries.
--
--   For $R=1$ this is Theorem 1.2. The relaxation to approximately uniform samples is what the quantum learning applications of §8.2 need.
--
--   **Formalization Note** Logarithms are base 2. Machine, success predicate and conventions are those of the published Theorem 1.2 (`AlgoPFR.theorem_1_2_algorithmic_pfr`). The program does not see $\mu$; it reads $n$, $\lceil K\rceil$, $\lceil R\rceil$ and $\lceil\log(1/\delta)\rceil$. A run is a tape whose samples lie in $A$.
--
--   Differences from the source:
--
--   - generalization: the algorithm knows K, R and δ → the program receives only ⌈K⌉, ⌈R⌉ and ⌈log₂(1/δ)⌉; reason: less input information, so a stronger existence claim that gives the printed one
--   - generalization: uses poly(n, K, R, log(1/δ)) time, samples, and membership queries → the bound holds on every run, not in expectation; reason: the stronger reading, as in the published Theorem 1.2; the proof runs a fixed number of walk steps per sample
--   - encoding: K^O(1) and poly(n, K, R, log(1/δ)) → C·K^c and C′(n + K + R + log₂(1/δ) + 2)^c′, constants before n, A, K, R, δ, μ; reason: one program for all inputs; the covering constant depends on neither R nor δ
--   - encoding: a randomized algorithm and 'time' → a program of the randomized log-cost oracle RAM of AlgoPFR.Machine; reason: the source names no model; the base mission fixes this one
--   - encoding: with probability at least 1 − δ → the success event contains a measurable event of measure ≥ 1 − δ; reason: inner measure, as in the base mission
--   - encoding: a basis for a subspace V → a linearly independent list L, with V = span L (IsPFROutput); reason: the same object, in the output encoding
-- source:
--   Arunachalam, Dutt, Grewal, Gupte, Marton's conjecture in polynomial time, arXiv:2609.20771 (sha256 60e45066…), Theorem 8.2, p.53 (proof: §8.1, pp.53–55)

import Mathlib
import Definitions.Def_AlgoPFR_Machine
import Definitions.Def_AlgoPFR_Supplement_IsRUniform

set_option autoImplicit false

open scoped ENNReal Pointwise

namespace AlgoPFR

namespace Supplement

/-- **Theorem 8.2 (Approximate algorithmic PFR).** Arunachalam, Dutt, Grewal, Gupte, *Marton's
conjecture in polynomial time*, arXiv:2609.20771 (sha256 60e45066…), p.53: let `0 < δ < 1`, and let
`A ⊆ F₂ⁿ` be nonempty with `|A + A| ≤ K|A|`. Given membership-oracle access to `A` and independent samples
from an `R`-uniform distribution on `A`, there is a randomized algorithm that, with probability at least
`1 − δ`, outputs a basis for a subspace `V ≤ F₂ⁿ` such that `|V| ≤ |A|` and `A` can be covered by at most
`K^{O(1)}` translates of `V`. It uses `poly(n, K, R, log(1/δ))` time, samples, and membership queries.

**Formalization Note.** The machine, the success predicate `IsPFROutput` and the conventions are those of
the published Theorem 1.2 (`AlgoPFR.theorem_1_2_algorithmic_pfr`). One program and the constants
`C, c, C′, c′` come before `n, A, K, R, δ, μ`; the covering constant `C K^c` depends on neither `R` nor `δ`.
The sample stream has law `μ`, any `R`-uniform law on `A` (Definition 8.1), which the program does not
see; it reads `[n, ⌈K⌉₊, ⌈R⌉₊, ⌈log₂(1/δ)⌉₊]`. The resource bound holds on every tape whose samples lie in
`A`. -/
theorem theorem_8_2_approximate_pfr :
    ∃ (P : Program) (C C' : ℝ) (c c' : ℕ), ∀ (n : ℕ) (A : Finset (Vec n)) (K R δ : ℝ)
      (μ : PMF (Vec n)), A.Nonempty → ((A + A).card : ℝ) ≤ K * A.card → IsRUniform μ A R →
      0 < δ → δ < 1 →
      (∀ ω : Tape n, IsRunTape A ω →
        HaltsWithin n P (memberRate A) [n, ⌈K⌉₊, ⌈R⌉₊, ⌈Real.logb 2 (1 / δ)⌉₊] ω
          (C' * ((n : ℝ) + K + R + Real.logb 2 (1 / δ) + 2) ^ c')) ∧
      ProbAtLeast (tapeMeasure μ)
        {ω | ∃ o, Outputs n P (memberRate A) [n, ⌈K⌉₊, ⌈R⌉₊, ⌈Real.logb 2 (1 / δ)⌉₊] ω o ∧
          IsPFROutput A K C c o} (1 - δ) := by sorry

end Supplement

end AlgoPFR
