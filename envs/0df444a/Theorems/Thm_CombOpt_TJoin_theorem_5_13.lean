-- Prove2me | Theorems.Thm_CombOpt_TJoin_theorem_5_13
-- name    : CombOpt.TJoin.theorem_5_13
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:07:21.865637+00:00
-- url     : https://prove2.me/theorems/25476bf3-22e8-47f0-9bef-29f41c059c1a
-- title:
--   Theorem 5.13 — Edmonds' perfect-matching LP: feasibility and optimal value (corrected: loopless)
-- statement:
--   Let $G=(V,E)$ be a graph without loops and $c\in\mathbb R^E$. Then
--
--   1. $G$ has a perfect matching if and only if the linear program (5.13)–(5.16) has a feasible solution;
--   2. if $G$ has a perfect matching, then the minimum weight of a perfect matching equals the optimal value of (5.13):
--
--   $$\min\{c(M): M \text{ a perfect matching}\}=\min\Big\{\sum_{e}c_ex_e:\ x(\delta(v))=1\ (v\in V),\ x(D)\ge1\ (D\in\mathcal C),\ x\ge0\Big\}.$$
--
--   This is Edmonds' theorem; it is the basis of the proof of Theorem 5.28 via a matching on the terminal set.
--
--   **Formalization Note** Both values are taken in the extended reals.
--
--   Differences from the source:
--   - correction: G a graph (loops allowed) → G has no loops (hloop); reason: counterexample: V = {a, b}, edges ab and a loop ℓ at a, c_ab = 0, c_ℓ = −1; the only perfect matching {ab} weighs 0, but ℓ lies in no δ(v) and no cut, so x_ℓ is free above 0 and (5.13) is unbounded below; parallel edges stay allowed
--   - encoding: the minimum weight of a perfect matching and the optimal value of (5.13) → infima in EReal; reason: under the hypothesis that a perfect matching exists both are finite; same instances
--   - encoding: for all D ∈ C → for all S with |S| odd and δ(S) ≠ δ(v) for every node v; reason: C is by definition the set of such cuts; the same constraint set
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Theorem 5.13, p. 148 (PDF p. 156)

import Mathlib
import Definitions.Def_CombOpt_TJoin_Graph
import Definitions.Def_CombOpt_TJoin_Graph_cut
import Definitions.Def_CombOpt_TJoin_Graph_IsPerfectMatching
import Definitions.Def_CombOpt_TJoin_Graph_minPerfectMatchingWeight
import Definitions.Def_CombOpt_TJoin_Graph_IsFeasible513
import Definitions.Def_CombOpt_TJoin_Graph_lpValue513

namespace CombOpt.TJoin

open scoped symmDiff

/-- **Theorem 5.13 (Edmonds' perfect-matching linear program), corrected: loopless.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), Theorem 5.13, p. 148 (PDF p. 156): "Let G be a graph, and let c ∈ R^E. Then G has a perfect
matching if and only if (5.13) has a feasible solution. Moreover, if G has a perfect matching,
then the minimum weight of a perfect matching is equal to the optimal value of (5.13)."

**Formalization Note.** `G` has no loops (`hloop`). The printed statement fails with a loop:
`V = {a, b}`, edges `ab` and a loop `ℓ` at `a`, `c_ab = 0`, `c_ℓ = −1`; the only perfect matching
`{ab}` weighs `0`, but `ℓ` is in no cut, so `x_ℓ` is free above `0` and (5.13) is unbounded
below. Values are in `EReal`. -/
theorem theorem_5_13 {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : Graph V E) (hloop : ∀ e, ¬ (G.ends e).IsDiag) (c : E → ℝ) :
    ((∃ M : Finset E, G.IsPerfectMatching M) ↔ ∃ x : E → ℝ, G.IsFeasible513 x) ∧
      ((∃ M : Finset E, G.IsPerfectMatching M) →
        G.minPerfectMatchingWeight c = G.lpValue513 c) := by sorry

end CombOpt.TJoin
