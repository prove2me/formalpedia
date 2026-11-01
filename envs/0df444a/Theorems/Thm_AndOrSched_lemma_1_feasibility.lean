-- Prove2me | Theorems.Thm_AndOrSched_lemma_1_feasibility
-- name    : AndOrSched.lemma_1_feasibility
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:31:23.481929+00:00
-- url     : https://prove2.me/theorems/40c34590-25f6-4275-a3e3-94bea4d48f30
-- title:
--   Proof of Lemma 1, p.8 — every $\beta$-schedule is feasible
-- statement:
--   Let the instance have acyclic AND-precedences, integer processing times $p_j\in\{0,1\}$ and no redundant OR-arcs, and let $x$ be a feasible solution of LP (1). Fix $0<\beta\le1$ and $\alpha=\beta/\Delta$, and sort the $A$-jobs by $t^\alpha_a$ and the $B$-jobs by $t^\beta_b$ with the paper's tie rules. Then
--   1. at least one order compatible with these keys and tie rules exists;
--   2. the schedule of every compatible order is feasible.
--
--   Differences from the source:
--   - generalization: x̄ an optimal solution of LP (1) → x any feasible solution of LP (1); reason: the argument uses only constraints (1b), (1d), (1e), (1f); optimal solutions are feasible
--   - encoding: "Break all other ties arbitrarily" → existence of a compatible order, and feasibility for every compatible order; reason: covers every tie-breaking and excludes a vacuous ∀
-- source:
--   F. Happach, A. S. Schulz, Approximation Algorithms and LP Relaxations for Scheduling Problems Related to Min-Sum Set Cover, arXiv:2001.07011v1, proof of Lemma 1, p.8, "We first show that scheduling the jobs in order of ≺ yields a feasible schedule for any fixed 0 < β ≤ 1."

import Mathlib
import Definitions.Def_AndOrSched_Instance
import Definitions.Def_AndOrSched_Acyclic
import Definitions.Def_AndOrSched_IsFeasible
import Definitions.Def_AndOrSched_orPred
import Definitions.Def_AndOrSched_nonRedPred
import Definitions.Def_AndOrSched_listC
import Definitions.Def_AndOrSched_Compat
import Definitions.Def_AndOrSched_LP1Feasible
import Definitions.Def_AndOrSched_key
open scoped Classical NNReal

namespace AndOrSched

/-- Proof of Lemma 1, p.8 (Happach, Schulz, arXiv:2001.07011v1): "We first show that scheduling the jobs in order of ≺ yields a
feasible schedule for any fixed 0 < β ≤ 1."

Let the instance have acyclic AND-precedences, integer processing times at most `1` and no
redundant OR-arcs, and let `x` be any feasible solution of LP (1). For every `β ∈ (0, 1]`, with
`α = β/Δ`, some order compatible with the `α`-points of the `A`-jobs, the `β`-points of the `B`-jobs
and the tie rules exists, and the schedule of every such order is feasible. -/
theorem lemma_1_feasibility (I : Instance) (hI : Acyclic I) (hint : ∀ j, ∃ n : ℕ, I.p j = n)
    (hp : ∀ j, I.p j ≤ 1) (hred : ∀ b, nonRedPred I b = orPred I b)
    (x : I.N → ℕ → ℝ) (hx : LP1Feasible I x) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    (∃ σ, Compat I (key I x β) σ) ∧
    ∀ σ, Compat I (key I x β) σ → IsFeasible I (listC I σ) := by sorry

end AndOrSched
