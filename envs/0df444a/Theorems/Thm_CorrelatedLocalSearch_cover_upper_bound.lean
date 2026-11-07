-- Prove2me | Theorems.Thm_CorrelatedLocalSearch_cover_upper_bound
-- name    : CorrelatedLocalSearch.cover_upper_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:38:23.833689+00:00
-- url     : https://prove2.me/theorems/f943a558-b6d1-47ab-a86b-599612d86dfb
-- title:
--   §2 — every cover bounds $\nu(E)$ by $D\sum_{w\in B}P[w]^s$
-- statement:
--   Let $s$ be real, $D\ge1$ and $\nu\in\mathcal Q_{s,D}$. If a finite set $B$ of words covers a tape event $E$, that is $E\subseteq\bigcup_{w\in B}[w]$, then
--   $$
--   \nu(E)\ \le\ D\sum_{w\in B}P[w]^s .
--   $$
--
--   This is the upper-bound half of the tree capacity identity (Theorem 2.1) and the only part of it the proof of Theorem 4.1 uses: every probability bound of the mission is obtained by exhibiting a cover.
--
--   **Formalization Note** $\nu(E)$ is the outer measure, so $E$ need not be measurable.
--
--   Differences from the source:
--   - generalization: finite prefix-free covers B of a closed event E → any finite set B of words covering any set E; reason: the bound uses only subadditivity and the prefix bound; prefix-free covers of closed events are a special case
-- source:
--   Xu, Local Search with Correlated Randomness, arXiv:2607.17469 (sha256 17e00d69…), §2 'Selectors, termination, and covers', p.6 (PDF p.8); App. B, proof of Theorem 2.1, first sentence, p.19 (PDF p.21)

import Mathlib
import Definitions.Def_CorrelatedLocalSearch_SourceClass

set_option autoImplicit false

namespace CorrelatedLocalSearch

open MeasureTheory

/-- The cover upper bound (Xu, *Local Search with Correlated Randomness*, arXiv:2607.17469
(sha256 17e00d69…), §2 "Selectors, termination, and covers", p.6: "Every cover gives an upper
bound on `ν(E)` for every `ν ∈ Q_{s,D}`, by summing the source bounds over its words"; also the
first sentence of the proof of Theorem 2.1, App. B, p.19): if a finite set `B` of words covers
`E`, then `ν(E) ≤ D Σ_{w∈B} P[w]^s` for every `ν ∈ Q_{s,D}`.

**Formalization Note** The paper's covers are finite and prefix-free and its `E` closed;
neither condition is needed for this direction, and both are dropped. `ν E` is the outer
measure, so `E` need not be measurable. -/
theorem cover_upper_bound (k : ℕ) (s D : ℝ) (hD : 1 ≤ D) (ν : Measure (ℕ → Fin k))
    (hν : ν ∈ SourceClass k s D) (E : Set (ℕ → Fin k)) (B : Finset (List (Fin k)))
    (hB : E ⊆ ⋃ w ∈ B, cyl w) :
    ν E ≤ ENNReal.ofReal (D * ∑ w ∈ B, refMass k w ^ s) := by sorry

end CorrelatedLocalSearch
