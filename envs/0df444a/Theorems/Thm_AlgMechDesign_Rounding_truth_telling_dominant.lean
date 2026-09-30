-- Prove2me | Theorems.Thm_AlgMechDesign_Rounding_truth_telling_dominant
-- name    : AlgMechDesign.Rounding.truth_telling_dominant
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T22:23:18.812185+00:00
-- url     : https://prove2.me/theorems/b6d0fc5f-8fdc-495f-8ce5-22f7e0d1e01c
-- title:
--   Proof of Theorem 5.9 — truth-telling is among the dominant strategies
-- statement:
--   Consider the rounding mechanism for bounded scheduling with times in $[a,b]$, $0 < a < b$, a rounding step $\delta > 0$, and an allocation algorithm that exactly solves the rounded problem (ties arbitrary). For every agent $i$ and every true type $t^i \in [a,b]^k$, the strategy that declares $t^i$ and performs every own task $j$ in its minimal time $t^i_j$ is dominant. In particular the rounding mechanism is truthful in the sense of Definition 19: every agent has a dominant strategy whose declaration is its true type.
--
--   **Formalization Note** Dominance is over the bounded space: the others' declarations and the agent's alternative declarations lie in $[a,b]^k$, the others' executions are arbitrary, and the agent's alternative executions are feasible for its true type.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, p. 193, proof (sketch) of Theorem 5.9, last sentence; p. 186, Definition 19

import Mathlib
import Definitions.Def_AlgMechDesign_Rounding_Model
import Definitions.Def_AlgMechDesign_Rounding_Mechanism

namespace AlgMechDesign.Rounding

/-- Proof of Theorem 5.9, last sentence (p. 193): in the rounding mechanism with an allocation
algorithm that exactly solves the rounded problem, truth-telling is among the dominant strategies:
for every agent `i` and true type `ti ∈ [a, b]ᵏ`, declaring `ti` and executing every own task in
its minimal time `tⁱ_j` is dominant. In particular the mechanism is truthful (Def. 19). -/
theorem truth_telling_dominant {n k : ℕ} [NeZero n] (a b δ : ℝ) (ha : 0 < a) (hab : a < b)
    (hδ : 0 < δ) (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (halloc : IsRoundedOptimal a b δ alloc) :
    (∀ (i : Fin n) (ti : Fin k → ℝ), IsBoundedAgentType a b ti →
      Dominant a b alloc (roundingPay δ alloc) i ti ti (fun _ => ti)) ∧
    Truthful a b alloc (roundingPay δ alloc) := by sorry

end AlgMechDesign.Rounding
