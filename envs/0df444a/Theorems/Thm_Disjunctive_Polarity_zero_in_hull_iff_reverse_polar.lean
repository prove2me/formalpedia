-- Prove2me | Theorems.Thm_Disjunctive_Polarity_zero_in_hull_iff_reverse_polar
-- name    : Disjunctive.Polarity.zero_in_hull_iff_reverse_polar
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T16:20:20.994343+00:00
-- url     : https://prove2.me/theorems/859f8f89-74ae-448e-b1b1-c2272f1d01f4
-- title:
--   Proposition 2.13 — when the reverse polar is empty or bounded
-- statement:
--   This is Proposition 2.13 of Balas's *Disjunctive Programming* (not found by
--   `statements.jsonl`'s regex extraction; verified directly against the PDF): the boundedness
--   criterion for reverse polars, contrasting sharply with ordinary polars (for which $S^0$ is
--   bounded iff $0 \in \mathrm{int}\,\mathrm{cl}\,\mathrm{conv}(S)$).
--
--   The following are equivalent: $0 \in \mathrm{cl}\,\mathrm{conv}(S)$; the reverse polar
--   $S^\# = \emptyset$; and $S^\#$ is bounded.
--
--   Intuitively, if some $x$ separates the origin from $\mathrm{cl}\,\mathrm{conv}(S)$ via
--   $xy \ge 1$ for all $y \in S$, then $S^\# \ne \emptyset$ and every positive multiple of $x$ also
--   works, so $S^\#$ is automatically unbounded whenever it is nonempty — hence "empty" and "bounded"
--   coincide for reverse polars.
--
--   **Formalization Note.** The three-way equivalence is stated with Mathlib's `List.TFAE`.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 32, Proposition 2.13

import Mathlib
import Definitions.Def_Disjunctive_Polarity_Polars

namespace Disjunctive.Polarity

/-- Proposition 2.13 (Balas §2.4, p. 32; not in `statements.jsonl`'s regex extraction): `0` lies
in the closed convex hull of `S` if and only if the reverse polar `S#` is empty, if and only if
`S#` is bounded. Stated for `n ≥ 1`: in `ℝ⁰` every set is bounded, so `S = ∅` has
`S# = {0}` bounded while `0 ∉ cl conv ∅`. -/
theorem zero_in_hull_iff_reverse_polar {n : ℕ} [NeZero n] (S : Set (Fin n → ℝ)) :
    List.TFAE [0 ∈ closure (convexHull ℝ S), ReversePolar S = ∅,
      Bornology.IsBounded (ReversePolar S)] := by sorry

end Disjunctive.Polarity
