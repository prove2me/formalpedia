-- Prove2me | Theorems.Thm_ArcFlowBPP_exact_cover_of_cover
-- name    : ArcFlowBPP.exact_cover_of_cover
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:07:06.298139+00:00
-- url     : https://prove2.me/theorems/a4d1a588-1521-4b62-9fed-8a22f4d57d84
-- title:
--   Proof of Property 1, p.7 — excess can be removed without increasing the number of rolls
-- statement:
--   Let $P \subseteq \mathbb N^m$ be a set of patterns closed under removing one item, and let $b$ be demands. For every feasible solution $x$ of the Gilmore–Gomory model (6)–(8) over $P$ there is a feasible solution $x'$ over $P$ that meets every demand exactly and uses at most as many rolls:
--
--   $$
--   \sum_{p\in P} p_i\, x'_p = b_i \quad (i = 1, \dots, m), \qquad \sum_{p\in P} x'_p \le \sum_{p\in P} x_p .
--   $$
--
--   This holds for the integer program and for its linear relaxation (two clauses). It is why the equality constraints (20) and the arc bounds (21) do not change the value of the arc-flow model.
--
--   Differences from the source:
--   - generalization: for every optimal solution with some excess there is a solution with the same objective value that satisfies the demand exactly → for every feasible solution there is an exactly covering feasible solution with at most the same objective value; reason: applied to an optimal solution, "at most" is "the same", so the page's claim is a special case
--   - generalization: a graph with all valid packing patterns represented as paths from s to t (paths correspond to every valid packing pattern, p.7) → RemovalClosed (pathPatterns G): removing one item from a path pattern gives a path pattern or the zero pattern; reason: this is the property the proof uses ("replacing the use of some patterns by other patterns that do not include the items … satisfied with excess"); every set of valid packing patterns ((9), (25), also with x ≤ b) without the empty pattern is closed under removing one item, so the paper's hypothesis implies it
--   - encoding: integer program and its linear relaxation → two clauses, one over ℕ and one over ℝ with f ≥ 0; reason: Lean convention; same programs
-- source:
--   Brandão, Pedroso, Bin Packing and Related Problems: General Arc-flow Formulation with Graph Compression, arXiv:1310.6887v1, proof of Property 1, p.7

import Mathlib
import Definitions.Def_ArcFlowBPP_RemovalClosed
import Definitions.Def_ArcFlowBPP_coverage
import Definitions.Def_ArcFlowBPP_numRolls
import Definitions.Def_ArcFlowBPP_GGFeasible

namespace ArcFlowBPP

/-- Brandão, Pedroso, *Bin Packing and Related Problems: General Arc-flow Formulation with Graph Compression*, arXiv:1310.6887v1, proof of Property 1, p.7: "for every optimal solution with some excess there is a
solution with the same objective value that satisfies the demand exactly; this solution can be
obtained by replacing the use of some patterns by other patterns that do not include the items
whose demands are being satisfied with excess (recall that every valid packing pattern is
represented in the graph)."

Let `P` be a set of patterns closed under removing one item (`ArcFlowBPP.RemovalClosed`). Every
feasible solution `x` of the Gilmore–Gomory model (6)–(8) over `P` yields a feasible solution
`x'` over `P` that meets every demand exactly, `∑_p pᵢ x'_p = bᵢ` for all `i`, and uses at most
as many rolls, `∑_p x'_p ≤ ∑_p x_p`. The first clause is the integer case, the second the linear
relaxation.

**Formalization Note.** The page states this for an optimal solution with "the same objective
value"; the statement here is for every feasible solution with "at most the same value", which
gives the page's claim when `x` is optimal. -/
theorem exact_cover_of_cover {m : ℕ} (P : Set (Fin m → ℕ)) (hP : RemovalClosed P)
    (b : Fin m → ℕ) :
    (∀ x : (Fin m → ℕ) →₀ ℕ, GGFeasible ℕ P b x →
      ∃ x' : (Fin m → ℕ) →₀ ℕ, GGFeasible ℕ P b x' ∧ (∀ i, coverage x' i = b i) ∧
        numRolls x' ≤ numRolls x) ∧
    (∀ x : (Fin m → ℕ) →₀ ℝ, GGFeasible ℝ P b x →
      ∃ x' : (Fin m → ℕ) →₀ ℝ, GGFeasible ℝ P b x' ∧ (∀ i, coverage x' i = (b i : ℝ)) ∧
        numRolls x' ≤ numRolls x) := by sorry

end ArcFlowBPP
