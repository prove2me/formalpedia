-- Prove2me | Theorems.Thm_AlgMechDesign_Rounding_rounds_like_truth_dominant
-- name    : AlgMechDesign.Rounding.rounds_like_truth_dominant
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T22:15:15.302932+00:00
-- url     : https://prove2.me/theorems/13884fb2-fc6c-4e8f-9399-017972a42284
-- title:
--   Proof of Theorem 5.9 — strategies with the true rounded values are dominant
-- statement:
--   Consider the rounding mechanism for bounded scheduling with times in $[a,b]$, $0 < a < b$, a rounding step $\delta > 0$, and an allocation algorithm that exactly solves the rounded problem (ties arbitrary). Let agent $i$ have true type $t^i \in [a,b]^k$, and consider a strategy of $i$ consisting of
--
--   1. a declaration $d^i \in [a,b]^k$ with the same rounded value as the true type, $\hat d^i = \hat t^i$, and
--   2. a feasible execution plan (every own task $j$ performed in time $\tilde t_j \ge t^i_j$) such that, for every decision $x$ and every task $j \in x^i$, the rounded actual time equals the rounded true time, $\hat{\tilde t}_j = \hat t^i_j$.
--
--   Then this strategy is dominant for agent $i$: against all declarations in $[a,b]$ and all executions of the other agents, it yields at least the utility of every other strategy of agent $i$.
--
--   This is the direction of the paper's characterization of dominant strategies that the implementation claim uses.
--
--   **Formalization Note** The paper asserts that these are the *only* dominant strategies; only the "if" direction is stated here. With arbitrary tie-breaking the "only if" direction can fail: for $n = 2$, $k = 1$, $a = 1$, $b = 2$, $\varepsilon = 1/4$, $\delta = 1/4$, and the allocation that gives the task to agent $1$ unless agent $2$'s rounded declaration is strictly smaller, an agent of true time $1.01$ (rounded $1.25$) who declares $1.5$ obtains the best possible utility against every declaration of the other agent, so this declaration is dominant although its rounded value differs.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, p. 193, proof (sketch) of Theorem 5.9, second sentence

import Mathlib
import Definitions.Def_AlgMechDesign_Rounding_Model
import Definitions.Def_AlgMechDesign_Rounding_Mechanism

namespace AlgMechDesign.Rounding

/-- Proof of Theorem 5.9, second sentence (p. 193), the "if" direction: in the rounding mechanism
with an allocation algorithm that exactly solves the rounded problem, every feasible strategy
`(di, ei)` of agent `i` of true type `ti ∈ [a, b]ᵏ` that declares a type in `[a, b]ᵏ` with the
same rounded value as `ti` and executes its tasks so that their rounded times equal the rounded
true times is dominant. -/
theorem rounds_like_truth_dominant {n k : ℕ} [NeZero n] (a b δ : ℝ) (ha : 0 < a) (hab : a < b)
    (hδ : 0 < δ) (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (halloc : IsRoundedOptimal a b δ alloc) (i : Fin n) (ti di : Fin k → ℝ) (ei : ExecPlan n k)
    (hti : IsBoundedAgentType a b ti) (hdi : IsBoundedAgentType a b di)
    (hei : FeasibleExec i ti ei) (hr : RoundsLikeTruth δ i ti di ei) :
    Dominant a b alloc (roundingPay δ alloc) i ti di ei := by sorry

end AlgMechDesign.Rounding
