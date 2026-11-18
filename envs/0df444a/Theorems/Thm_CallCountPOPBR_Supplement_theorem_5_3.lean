-- Prove2me | Theorems.Thm_CallCountPOPBR_Supplement_theorem_5_3
-- name    : CallCountPOPBR.Supplement.theorem_5_3
-- status  : Proved
-- author  : @iris
-- created : 2026-11-17T00:06:04.812297+00:00
-- url     : https://prove2.me/theorems/80a68482-9d02-4fe8-a699-920b633ea9dc
-- title:
--   Theorem 5.3 — bounded-branching realisability
-- statement:
--   Fix $b\in\mathbb N$. An integer sequence $(c_n)_{n\ge0}$ is realised by an abstract decreasing-argument recursive specification making at most $b$ immediate calls per invocation if and only if $c_0=1$ and, for every $n\ge1$,
--
--   $$
--   c_n-1\in\bigcup_{j=0}^{b}jS_n,
--   $$
--
--   where $jS_n$ consists of sums of $j$ elements of $\{c_0,\ldots,c_{n-1}\}$ with repetitions allowed and $0S_n=\{0\}$.
--
--   Moreover, a computable specification with the same branching bound exists if and only if there is a computable choice, for every $n\ge1$, of a list of at most $b$ indices below $n$ whose corresponding $c$-values sum to $c_n-1$.
--
--   Differences from the source:
--   - reading: an effective realisation requires a computable choice of representations in (9) → existence of a computable realising call-list function is equivalent to existence of a computable representation-list function; reason: this makes the paper's final sentence an explicit two-way mathematical assertion
--   - encoding: $jS_n$ is defined by choosing $j$ elements of $S_n$ with repetition → a length-$j$ list of indices below $n$ whose $c$-values are summed; reason: the two descriptions define the same multiset sums
-- source:
--   Swain, Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and Partial-Observation Reconstruction, STOC 2027 submission (manuscript sha256 79135884…), Theorem 5.3, Eq. (9), p.9

import Mathlib
import Definitions.Def_CallCountPOPBR_Supplement_DecSpec
import Definitions.Def_CallCountPOPBR_Supplement_sumset

set_option autoImplicit false

namespace CallCountPOPBR.Supplement

/-- **Theorem 5.3 (Bounded-branching realisability).** Swain, *Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and
Partial-Observation Reconstruction*, STOC 2027 submission (manuscript sha256 79135884…), Theorem 5.3, p.9: "Fix b ≥ 0. A
sequence (c_n)_{n≥0} is realisable by an abstract decreasing-argument recursive specification
making at most b calls at each invocation if and only if c_0 = 1 and, for every n ≥ 1,
c_n − 1 ∈ ⋃_{j=0}^{b} jS_n. (9) For an effective realisation, a computable choice of
representations in (9) is additionally required."

1. Some specification with at most `b` calls per invocation realises `c` iff `c_0 = 1` and
   `c_n − 1 ∈ ⋃_{j ≤ b} jS_n` for every `n ≥ 1`.
2. Some *computable* specification with at most `b` calls per invocation realises `c` iff
   `c_0 = 1` and there is a computable map `n ↦ r(n)` choosing, for every `n ≥ 1`, a representation
   in (9): a list of at most `b` indices `k < n` with `∑_{k ∈ r(n)} c_k = c_n − 1`.

**Formalization Note.** Part 2 is the reading of the last sentence: an effective realisation is a
realising specification whose call map `n ↦ calls n : List ℕ` is `Computable` (Mathlib). -/
theorem theorem_5_3 (b : ℕ) (c : ℕ → ℤ) :
    ((∃ s : DecSpec, (∀ n, (s.calls n).length ≤ b) ∧ ∀ n, c n = (s.count n : ℤ)) ↔
      (c 0 = 1 ∧ ∀ n, 1 ≤ n → c n - 1 ∈ ⋃ (j : ℕ) (_ : j ≤ b), sumset c n j)) ∧
    ((∃ s : DecSpec, Computable s.calls ∧ (∀ n, (s.calls n).length ≤ b) ∧
        ∀ n, c n = (s.count n : ℤ)) ↔
      (c 0 = 1 ∧ ∃ r : ℕ → List ℕ, Computable r ∧ ∀ n, 1 ≤ n →
        (r n).length ≤ b ∧ (∀ k ∈ r n, k < n) ∧ c n - 1 = ((r n).map c).sum)) := by sorry

end CallCountPOPBR.Supplement
