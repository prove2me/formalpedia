-- Prove2me | Theorems.Thm_ConvexRMDP_feasible_set_convex
-- name    : ConvexRMDP.feasible_set_convex
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:17:57.307516+00:00
-- url     : https://prove2.me/theorems/1afcb22a-7faf-41f9-a523-a1421c3daee0
-- title:
--   Proof of Theorem 4.1: the feasible set $\{x \mid 1 \le x_s \le \tilde t(x)_s\}$ of (4.7) is convex
-- statement:
--   Let $(\mathcal S, \mathcal A, r, \gamma, \mathcal U)$ be an sa-rectangular robust MDP and $b > 0$. The feasible set of the program (4.7),
--   $$
--   \{x \in \mathbb R^{\mathcal S} \mid 1 \le x_s \le \tilde t(x)_s,\ \forall s \in \mathcal S\},
--   $$
--   the intersection of the half-spaces $\{x_s \ge 1\}$ with the set $\{x \le \tilde t(x)\}$, is convex.
--
--   Since the objective $\sum_s x_s$ of (4.7) is linear, this makes (4.7) a convex program.
--
--   Differences from the source:
--   - generalization: min over p ∈ 𝒰_sa (the paper's min presupposes attainment) → infimum (sInf) over an arbitrary nonempty 𝒰_sa ⊆ Δ(S); reason: the set is nonempty and bounded below; whenever the minimum is attained the infimum equals it, so the statement specializes to the source's.
--   - reading: 𝒰_sa ⊆ Δ(S) with min_{p ∈ 𝒰_sa} → 𝒰_sa nonempty (field U_nonempty of RMDP); reason: a minimum over an empty set is undefined; the paper's formulas presuppose nonemptiness.
--   - reading: the set {x ∈ ℝ^S | x ≤ t̃(x)} is convex → only the intersection {x | 1 ≤ x_s ≤ t̃(x)_s ∀ s} is claimed convex; reason: t̃ is defined on (ℝ*₊)^S only, so the paper's set lives in the positive orthant; its convexity there is the second clause of change_of_variables.
-- source:
--   Grand-Clément & Petrik, On the Convex Formulations of Robust Markov Decision Processes, arXiv:2209.10187v2 (13 Dec 2023), proof of Theorem 4.1, p.14, "The optimization problem in (4.7) is convex …"

import Mathlib
import Definitions.Def_ConvexRMDP_RMDP_tOp

namespace ConvexRMDP

/-- **The feasible set of (4.7) is convex** (Grand-Clément & Petrik, arXiv:2209.10187v2, p.14, proof
of Theorem 4.1, "The optimization problem in (4.7) is convex …"): the set
`{x ∈ ℝ^S | 1 ≤ x_s ≤ t̃(x)_s, ∀ s}`, the intersection of `{x | x_s ≥ 1 ∀ s}` and `{x | x ≤ t̃(x)}`,
is convex.

**Formalization Note.** `t̃` is defined on `(ℝ*₊)^S`, so the second set is read on positive vectors
and the statement is about the intersection (where `x ≥ 1`). `b > 0`. -/
theorem feasible_set_convex {S A : Type*} [Fintype S] [Fintype A]
    (M : RMDP S A) (b : ℝ) (hb : 0 < b) :
    Convex ℝ {x : S → ℝ | ∀ s, 1 ≤ x s ∧ x s ≤ M.tOp b x s} := by sorry

end ConvexRMDP
