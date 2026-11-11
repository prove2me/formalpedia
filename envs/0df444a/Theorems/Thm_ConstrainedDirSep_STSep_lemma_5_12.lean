-- Prove2me | Theorems.Thm_ConstrainedDirSep_STSep_lemma_5_12
-- name    : ConstrainedDirSep.STSep.lemma_5_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:05:51.005229+00:00
-- url     : https://prove2.me/theorems/2d124e63-27f9-4e8d-ac6a-7d34d74bb546
-- title:
--   Lemma 5.12 — chain lemma: the active marked points of each direction form increasing chains
-- statement:
--   Fix a pair of variables with domains $[d_i]$, $[d_j]$, a finite set $Q$ of quadrant constraints (thresholds in the ranges of (1)–(2)) with window $W$, and sets $F,B\subseteq[d_i]\times[d_j]$. Suppose
--
--   (i) $Q^{\searrow}_{p+1,q-1}\in Q$ for every $(p,q)\in F$ with this constraint nonvacuous, and
--   (ii) $Q^{\nwarrow}_{p-1,q+1}\in Q$ for every $(p,q)\in B$ with this constraint nonvacuous.
--
--   Then $F\cap W$ and $B\cap W$ are increasing chains in the coordinatewise order on $[d_i]\times[d_j]$.
--
--   This is property (R4) of the representation theorem: the input arcs between two candidate lists that can occur in a solution are ordered.
--
--   Differences from the source:
--   - generalization: F_ij, B_ij the marked sets of a representation (input arcs between candidates) → arbitrary F, B ⊆ [d_i] × [d_j]; reason: the proof uses only hypotheses (i) and (ii), and the marked sets are an instance.
-- source:
--   Olkowski, Ramanujan, Constrained Directed Separation: Algorithms and Classifications, STOC 2027 submission (manuscript sha256 4dd06c29…), p. 24 (PDF 27), Lemma 5.12

import Mathlib
import Definitions.Def_ConstrainedDirSep_STSep_Quadrant

namespace ConstrainedDirSep.STSep

/-- Olkowski, Ramanujan, *Constrained Directed Separation*, STOC 2027 submission (manuscript
sha256 4dd06c29…), p. 24 (PDF 27), Lemma 5.12 (Chain lemma): fix `i < j`; if (i)
`Q↘_{p+1,q−1} ∈ Q_ij` for every `(p, q) ∈ F_ij` with this constraint nonvacuous, and (ii)
`Q↖_{p−1,q+1} ∈ Q_ij` for every `(p, q) ∈ B_ij` with this constraint nonvacuous, then
`F_ij ∩ W_ij` and `B_ij ∩ W_ij` are chains in the coordinatewise order on `[d_i] × [d_j]`. -/
theorem lemma_5_12 (Q : Finset Quadrant) (di dj : ℕ)
    (hQ : ∀ c ∈ Q, c.WellRanged di dj)
    (F B : Set (ℕ × ℕ))
    (hF : ∀ pq ∈ F, 1 ≤ pq.1 ∧ pq.1 ≤ di ∧ 1 ≤ pq.2 ∧ pq.2 ≤ dj)
    (hB : ∀ pq ∈ B, 1 ≤ pq.1 ∧ pq.1 ≤ di ∧ 1 ≤ pq.2 ∧ pq.2 ≤ dj)
    (h1 : ∀ pq ∈ F, (Quadrant.se (pq.1 + 1) (pq.2 - 1)).Nonvacuous di dj →
      Quadrant.se (pq.1 + 1) (pq.2 - 1) ∈ Q)
    (h2 : ∀ pq ∈ B, (Quadrant.nw (pq.1 - 1) (pq.2 + 1)).Nonvacuous di dj →
      Quadrant.nw (pq.1 - 1) (pq.2 + 1) ∈ Q) :
    IsIncreasingChain (F ∩ window Q di dj) ∧ IsIncreasingChain (B ∩ window Q di dj) := by sorry

end ConstrainedDirSep.STSep
