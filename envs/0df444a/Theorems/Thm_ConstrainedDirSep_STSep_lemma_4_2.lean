-- Prove2me | Theorems.Thm_ConstrainedDirSep_STSep_lemma_4_2
-- name    : ConstrainedDirSep.STSep.lemma_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:05:49.421617+00:00
-- url     : https://prove2.me/theorems/83c0541d-db39-4769-bb6e-fafac5d4143b
-- title:
--   Lemma 4.2 — windows are staircases L(p) ≤ q ≤ U(p) with L, U nondecreasing
-- statement:
--   Let $Q$ be a finite set of quadrant constraints on a pair of variables with domains $[d_i]$ and $[d_j]$, with thresholds in the ranges of (1)–(2), let $W$ be its window and $L,U$ the staircase boundaries (7)–(8). Then $L$ and $U$ are nondecreasing on $[d_i]$, and for every $p\in[d_i]$
--   $$1\le L(p)\le d_j+1,\qquad 0\le U(p)\le d_j,$$
--   and for every $(p,q)\in[d_i]\times[d_j]$, $(p,q)\in W$ if and only if $L(p)\le q\le U(p)$.
--
--   The lemma turns the window of a pair of Chain CSP variables into a monotone staircase; it gives property (R3) of the representation theorem and is used for Lemma 4.3.
--
--   Differences from the source:
--   - generalization: d_i, d_j ≥ 1 (domains of a Chain CSP) → any d_i, d_j ≥ 0; reason: at d_i = 0 every clause is vacuous, and the source instance is the case d_i, d_j ≥ 1.
--   - encoding: L, U as integers on [d_i] → ℤ-valued functions on ℕ, "nondecreasing" as MonotoneOn on [1, d_i]; reason: Lean convention; same values on [d_i].
-- source:
--   Olkowski, Ramanujan, Constrained Directed Separation: Algorithms and Classifications, STOC 2027 submission (manuscript sha256 4dd06c29…), p. 16 (PDF 19), Lemma 4.2 (proof p. 41, PDF 44)

import Mathlib
import Definitions.Def_ConstrainedDirSep_STSep_Quadrant

namespace ConstrainedDirSep.STSep

/-- Olkowski, Ramanujan, *Constrained Directed Separation*, STOC 2027 submission (manuscript
sha256 4dd06c29…), p. 16 (PDF 19), Lemma 4.2: the staircase functions `L`, `U` of (7)–(8) are
nondecreasing, `1 ≤ L(p) ≤ d_j + 1`, `0 ≤ U(p) ≤ d_j`, and `(p, q) ∈ W_ij ⇔ L(p) ≤ q ≤ U(p)`. -/
theorem lemma_4_2 (Q : Finset Quadrant) (di dj : ℕ)
    (hQ : ∀ c ∈ Q, c.WellRanged di dj) :
    MonotoneOn (lowerL Q) (Set.Icc 1 di) ∧
    MonotoneOn (upperU Q dj) (Set.Icc 1 di) ∧
    (∀ p : ℕ, 1 ≤ p → p ≤ di →
      1 ≤ lowerL Q p ∧ lowerL Q p ≤ (dj : ℤ) + 1 ∧ 0 ≤ upperU Q dj p ∧ upperU Q dj p ≤ (dj : ℤ)) ∧
    ∀ p q : ℕ, 1 ≤ p → p ≤ di → 1 ≤ q → q ≤ dj →
      ((p, q) ∈ window Q di dj ↔ lowerL Q p ≤ (q : ℤ) ∧ (q : ℤ) ≤ upperU Q dj p) := by sorry

end ConstrainedDirSep.STSep
