-- Prove2me | Theorems.Thm_AlgMechDesign_Local_own_set_unchanged
-- name    : AlgMechDesign.Local.own_set_unchanged
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T19:55:19.221979+00:00
-- url     : https://prove2.me/theorems/ba1be7a7-ed46-4d55-8c7c-6521a87b9d94
-- title:
--   Claim 4.14, proof, first step — lowering an agent's times on its own set keeps that set
-- statement:
--   Let $(x, p)$ be a truthful mechanism for task scheduling, $t$ a positive type vector and $i$ an agent such that $x^i(t)$ is the unique maximizer of $i$'s utility among the sets attainable against $t^{-i}$. Let $0 < \varepsilon$ with $\varepsilon \le t^i_j$ for every task $j \in x^i(t)$, and let
--   $$
--   \hat t = t\bigl(x^i(t) \xrightarrow{i} \varepsilon\bigr)
--   $$
--   be $t$ with agent $i$'s time on each task of $x^i(t)$ lowered to $\varepsilon$. Then $x^i(\hat t) = x^i(t)$.
--
--   In the proof of Theorem 4.12 this is the first half of Claim 4.14: the agent whose times were lowered keeps its set, so the other agents only need to choose among sets disjoint from it.
--
--   **Formalization Note** The paper applies the step at $t^i_j = 1$ with $0 < \varepsilon < 1$; after the perturbation of Lemma 4.13 the type vector is only near $1$, so the condition is stated as $\varepsilon \le t^i_j$ on the tasks of $x^i(t)$.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, p. 181, proof of Claim 4.14, first sentence ("Clearly x²(t̂) = x²(t)")

import Mathlib
import Definitions.Def_AlgMechDesign_Local_Model
import Definitions.Def_AlgMechDesign_Local_Prices

namespace AlgMechDesign.Local

/-- Proof of Claim 4.14, p. 181, first step ("Clearly x²(t̂) = x²(t)"): for a truthful mechanism,
if at the positive type vector `t` the set `xⁱ(t)` is the unique maximizer of agent `i`'s
utility, then lowering agent `i`'s times on the tasks of `xⁱ(t)` to `ε`
(`0 < ε ≤ tⁱ_j` for those tasks) leaves agent `i`'s set unchanged. -/
theorem own_set_unchanged {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → Fin n → ℝ) (htr : IsTruthful alloc pay)
    (t : Fin n → Fin k → ℝ) (ht : IsType t) (i : Fin n)
    (huniq : IsUniqueMaximizer alloc pay t i) (ε : ℝ) (hε : 0 < ε)
    (hle : ∀ j ∈ agentSet alloc t i, ε ≤ t i j) :
    agentSet alloc (setTimes t i (agentSet alloc t i) ε) i = agentSet alloc t i := by sorry

end AlgMechDesign.Local
