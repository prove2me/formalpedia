-- Prove2me | Theorems.Thm_ComplementsRev_Approx_theorem_3_2
-- name    : ComplementsRev.Approx.theorem_3_2
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-10-18T22:15:50.365083+00:00
-- url     : https://prove2.me/theorems/ceac1b7d-a8cc-4f83-88c8-0e0e1237fbaf
-- title:
--   Theorem 3.2 — revenue approximation with complementarity d
-- statement:
--   Let $D$ be a finite product population of nonnegative hyperedge weights with fixed downward-closed feasibility constraints, and suppose every item belongs to at most $d$ hyperedges that can have positive weight. For every truthful, individually rational lottery mechanism $m$ on the induced valuation types,
--
--   $$\operatorname{Rev}(m)\le(4d+16)\max\{\operatorname{BREV}(D),\operatorname{SREV}^{*}(D)\}.$$
--
--   Thus the better of selling the grand bundle and the paper's conservative separate-item pricing earns at least a $1/(4d+16)$ fraction of any such mechanism's revenue.
--
--   **Formalization Note** The statement compares every mechanism with the two simple benchmarks, avoiding a real supremum over mechanisms. Individual rationality is included because incentive compatibility alone allows arbitrarily high constant payments.
-- source:
--   Eden, Feldman, Friedler, Talgam-Cohen & Weinberg, A Simple and Approximately Optimal Mechanism for a Buyer with Complements, arXiv:1612.04746v2, Theorem 3.2, p. 6

import Mathlib
import Definitions.Def_ComplementsRev_Approx_Setting

namespace ComplementsRev.Approx

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Eden et al., Theorem 3.2, p. 6: bundling or separate prices approximate revenue. -/
theorem theorem_3_2 (P : Population ι) (d : ℕ) (hd : HasComplementarity P d)
    (m : Mech ι) (hm : IsTruthful P m) :
    revenue P m ≤ (4 * (d : ℝ) + 16) * max (BREV P) (SREVstar P) := by sorry

end ComplementsRev.Approx
