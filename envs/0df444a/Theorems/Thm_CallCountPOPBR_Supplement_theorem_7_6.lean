-- Prove2me | Theorems.Thm_CallCountPOPBR_Supplement_theorem_7_6
-- name    : CallCountPOPBR.Supplement.theorem_7_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T00:07:28.010624+00:00
-- url     : https://prove2.me/theorems/1f778ed7-d1fb-4682-b19d-087758e666fc
-- title:
--   Theorem 7.6 — exact binary identifiability criterion
-- statement:
--   Fix $\beta\ge1$ and a sequence $c:\mathbb N\to\mathbb N$ with $c_n=1$ for $n<\beta$. In the full-binary model, exactly one unordered dependency specification realises $c$ if and only if
--
--   $$
--   |P_n|=1\qquad\text{for every }n\ge\beta,
--   $$
--
--   where $P_n$ consists of unordered pairs $\{i,j\}$ with repetition allowed, $i,j<n$, and $c_i+c_j+1=c_n$.
--
--   More generally, if $c$ is realisable, then at every $n\ge\beta$ the set of child pairs chosen at $n$ among all realising specifications is exactly $P_n$, and therefore has cardinality $|P_n|$. If $P_n$ is empty at any such input, no specification realises $c$.
--
--   Differences from the source:
--   - encoding: unordered pairs $\{i,j\}$ with $0\le i\le j<n$ → elements of $\operatorname{Sym}^2(\operatorname{Fin} n)$, with the compatibility equation written $c_i+c_j+1=c_n$; reason: the symmetric square represents repetition-permitting unordered pairs and the equation avoids truncated natural subtraction
--   - reading: the number of compatible choices at $n$ is $|P_n|$, and zero means non-realisability → the set of values at $n$ across all globally realising specifications equals $P_n$, plus the explicit no-realisation clause; reason: this is the exact set-level assertion proved in the paper and implies the stated cardinality conclusions
-- source:
--   Swain, Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and Partial-Observation Reconstruction, STOC 2027 submission (manuscript sha256 79135884…), Theorem 7.6, p.13

import Mathlib
import Definitions.Def_CallCountPOPBR_Supplement_BinSpec

set_option autoImplicit false

namespace CallCountPOPBR.Supplement

/-- **Theorem 7.6 (Exact binary identifiability criterion).** Swain, *Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and
Partial-Observation Reconstruction*, STOC 2027 submission (manuscript sha256 79135884…), Theorem 7.6, p.13: "In the
full-binary model with base set {0, . . . , β−1}, a call-count sequence (c_n) determines the entire
unordered dependency multigraph uniquely if and only if |P_n| = 1 for every n ≥ β. More generally,
at each input n ≥ β the number of compatible choices of its unordered pair of children is exactly
|P_n|; a zero cardinality means that the sequence is not realisable in this model."

For `β ≥ 1` and a sequence `c` (`s` realises `c` when `s.count n = c n` for all `n`):
1. if `c_n = 1` for `n < β`, exactly one specification realises `c` iff `|P_n| = 1` for every
   `n ≥ β`;
2. if `c` is realisable, then at every `n ≥ β` the child pairs chosen at `n` by the realising
   specifications form exactly the set `P_n` (so there are exactly `|P_n|` of them);
3. if `P_n = ∅` for some `n ≥ β`, no specification realises `c`.

    **Formalization Note.** A specification is the unordered dependency multigraph itself
    (`BinSpec β`, data only at `n ≥ β`), so uniqueness is uniqueness of the multigraph. The base
    values `c_n = 1` (`n < β`) are the standing condition of the full-binary model and make `c` a
    candidate call-count sequence of that model. -/
    theorem theorem_7_6 (β : ℕ) (hβ : 1 ≤ β) (c : ℕ → ℕ)
        (hbase : ∀ n, n < β → c n = 1) :
        ((∃! s : BinSpec β, ∀ n, s.count n = c n) ↔
          ∀ n, β ≤ n → (pairSet c n).card = 1) ∧
    ((∃ s : BinSpec β, ∀ n, s.count n = c n) →
      ∀ n (h : β ≤ n),
        {z | ∃ s : BinSpec β, (∀ m, s.count m = c m) ∧ s n h = z} = (pairSet c n : Set (Sym2 (Fin n)))) ∧
    (∀ n, β ≤ n → pairSet c n = ∅ → ¬ ∃ s : BinSpec β, ∀ m, s.count m = c m) := by sorry

end CallCountPOPBR.Supplement
