-- Prove2me | Theorems.Thm_BarelyTestable_LowerBound_main_theorem
-- name    : BarelyTestable.LowerBound.main_theorem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:21:57.321398+00:00
-- url     : https://prove2.me/theorems/ebd6f3d1-d89c-48f4-9b00-64b81320d5f4
-- title:
--   Theorem 1.1 — exponential worst-case query lower bound
-- statement:
--   For every fixed $0<\varepsilon<10^{-8}$ there is $N_0$ such that for every $n\ge N_0$, every randomized adaptive two-sided tester for submodularity at dimension $n$ and every finite worst-case query budget $q$ for that tester satisfy
--
--   $$q\ge2^{\sqrt n/5}.$$
--
--   Every submodular real oracle must be accepted with probability at least $2/3$, and every oracle whose exact normalized Hamming distance from every real submodular repair is at least $\varepsilon$ must be rejected with probability at least $2/3$. Seeds range over an arbitrary probability space independent of the oracle. The budget applies to every oracle and every seed. There is no finite-range, nonnegative, normalized, monotone or nonadaptive restriction. Unbounded worst-case query cost also satisfies the lower-bound assertion, since it has no finite universal budget. Theorem 3.1 on p.11 is the same target.
--
--   Differences from the source:
--   - encoding: Boolean vectors with coordinates numbered from 1 → finite subsets of Fin n, numbered from 0; reason: the incidence-vector bijection preserves every vertex, union, intersection and coordinate square
--   - reading: Theorem 1.1 with Definition 2.5, and the p.11 padding observation → the stated exponent bound holds for every sufficiently large dimension; reason: p.26 proves the construction dimensions; projection, slice mismatch counting and m=floor(sqrt((n−2)/2)) preserve the exact exponent using the intermediate 2^(m/2)/10 margin
--   - generalization: a family of ε-testers whose correctness starts at its own dimension threshold → N₀ is uniform over all protocols correct at each fixed n; reason: the distributions and estimates are uniform over algorithms; for a family take the maximum of N₀ and its correctness threshold
--   - encoding: maximum queries over all functions and random choices → every finite universal budget q is at least the displayed real lower bound; reason: natural budgets give the ceiling of the real target; absence of any finite budget represents infinite cost without a default finite supremum
--   - encoding: a randomized algorithm with a random seed and probabilities of acceptance/rejection → a Tester on an arbitrary measurable seed space whose acceptance and rejection events are measurable for each oracle; reason: measurability only makes the source's probabilities defined; every source tester has defined acceptance probabilities
-- source:
--   Diptaksho Palit, Yuichi Yoshida, STOC 2027 submission #722 (October 2026), Theorem 1.1, p. 2 (printed = PDF page); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/722.pdf; PDF SHA256 a095e6ef801edf5b0ce3967efca977e04b7a0b4374e874116509d73837bd14f3

import Mathlib
import Definitions.Def_BarelyTestable_LowerBound_Protocol

set_option autoImplicit false

namespace BarelyTestable.LowerBound

open NonmonotoneSubmod.Shared MeasureTheory

/-- Theorem 1.1, p.2 = Theorem 3.1, p.11, with all-large-dimension padding from p.11.
The lower bound is uniform over fixed-dimension protocols; infinite worst-case costs are
represented by absence of a finite universal budget. -/
theorem main_theorem (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < (1/10^8 : ℝ)) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (T : Tester (Fin n) Ω) (q : ℕ),
        Correct μ T Submodular ε → TesterBudget T q →
          (2 : ℝ) ^ (Real.sqrt (n : ℝ) / 5) ≤ (q : ℝ) := by sorry

end BarelyTestable.LowerBound
