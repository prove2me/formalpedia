-- Prove2me | Theorems.Thm_BoundedParamMDP_Optimal_theorem9_bellman_equations
-- name    : BoundedParamMDP.Optimal.theorem9_bellman_equations
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:05:03.962985+00:00
-- url     : https://prove2.me/theorems/5f77403c-cd0f-4e57-9fac-2557c0a426f3
-- title:
--   Theorem 9 — Bellman-like equations (25)–(26) for $V_\updownarrow{}_{\mathrm{opt}}$ and $V_\updownarrow{}_{\mathrm{pes}}$
-- statement:
--   Let $M_\updownarrow$ be a bounded-parameter MDP over finite $Q$ and a finite nonempty action set $A$, with discount rate $0\le\gamma<1$. Let $V_\updownarrow{}_{\mathrm{opt}}=[V_\downarrow{}_{\mathrm{opt}},V_\uparrow{}_{\mathrm{opt}}]$ be the optimistic optimal interval value function, i.e. $V_\updownarrow{}_{\pi_{\mathrm{opt}}}$ for an optimistically optimal policy $\pi_{\mathrm{opt}}$ (Definition 8). Then at every state $p$,
--   $$
--   V_\updownarrow{}_{\mathrm{opt}}(p)=\max_{\alpha\in A,\ \le_{\mathrm{opt}}}\Big[\min_{M\in M_\updownarrow}VI_{M,\alpha}(V_\downarrow{}_{\mathrm{opt}})(p),\ \max_{M\in M_\updownarrow}VI_{M,\alpha}(V_\uparrow{}_{\mathrm{opt}})(p)\Big], \tag{25}
--   $$
--   and, for the pessimistic optimal interval value function $V_\updownarrow{}_{\mathrm{pes}}=V_\updownarrow{}_{\pi_{\mathrm{pes}}}$ of a pessimistically optimal policy $\pi_{\mathrm{pes}}$,
--   $$
--   V_\updownarrow{}_{\mathrm{pes}}(p)=\max_{\alpha\in A,\ \le_{\mathrm{pes}}}\Big[\min_{M\in M_\updownarrow}VI_{M,\alpha}(V_\downarrow{}_{\mathrm{pes}})(p),\ \max_{M\in M_\updownarrow}VI_{M,\alpha}(V_\uparrow{}_{\mathrm{pes}})(p)\Big]. \tag{26}
--   $$
--   The maximum is taken over the actions with respect to the total order $\le_{\mathrm{opt}}$ (resp. $\le_{\mathrm{pes}}$) on intervals: the interval on the left is the interval of some action, and it is $\ge_{\mathrm{opt}}$ (resp. $\ge_{\mathrm{pes}}$) the interval of every action.
--
--   These equations are the interval analogue of the Bellman optimality equation, and they are the basis of the interval value iteration algorithms $IVI_\updownarrow{}_{\mathrm{opt}}$ and $IVI_\updownarrow{}_{\mathrm{pes}}$ of Section 5.
--
--   **Formalization Note** Definition 8 defines $V_\updownarrow{}_{\mathrm{opt}}$ as the $\le_{\mathrm{opt}}$-maximum of $V_\updownarrow{}_\pi$ over policies, which exists by Theorem 8 and is unique because $\le_{\mathrm{opt}}$ is antisymmetric on intervals; the statement therefore quantifies over every optimistically optimal policy $\pi_{\mathrm{opt}}$ and uses $V_\updownarrow{}_{\pi_{\mathrm{opt}}}$ (likewise for $\pi_{\mathrm{pes}}$). The inner minima and maxima over $M\in M_\updownarrow$ are written as the real infimum and supremum over the members (they are attained, but the theorem does not need that). Intervals are pairs (lower, upper). Policies are deterministic stationary maps $Q\to A$.
-- source:
--   Givan, Leach, Dean, Bounded-parameter Markov decision processes, Artificial Intelligence (2000), manuscript of May 22, 2000, pp. 18–19, Theorem 9, eqs. (25)–(26); Definition 8, p. 18

import Mathlib
import Definitions.Def_BoundedParamMDP_Optimal_MDP
import Definitions.Def_BoundedParamMDP_Optimal_BMDP

namespace BoundedParamMDP.Optimal

/-- Theorem 9 (pp. 18–19), equations (25) and (26). For an optimistically optimal `π_opt`
(so `V↕opt = V↕π_opt`, Definition 8) and every state `p`, the interval
`V↕opt(p) = [V↓opt(p), V↑opt(p)]` is the `≤_opt`-maximum over actions `α` of
`[min_{M ∈ M↕} VI_{M,α}(V↓opt)(p), max_{M ∈ M↕} VI_{M,α}(V↑opt)(p)]`: it is attained at some
action and `≤_opt`-dominates the interval of every action. Likewise for a pessimistically
optimal `π_pes` with `≤_pes`. -/
theorem theorem9_bellman_equations {Q A : Type*} [Fintype Q] [DecidableEq Q] [Fintype A]
    [Nonempty A] (B : BMDP Q A) :
    (∀ πo : Policy Q A, IsOptOptimal B πo → ∀ p : Q,
      (∃ α : A, ((⨅ M : Member B, VIact M.1 α (lowerV B πo) p),
          (⨆ M : Member B, VIact M.1 α (upperV B πo) p)) = intervalV B πo p) ∧
      ∀ α : A, optLE ((⨅ M : Member B, VIact M.1 α (lowerV B πo) p),
          (⨆ M : Member B, VIact M.1 α (upperV B πo) p)) (intervalV B πo p)) ∧
    (∀ πp : Policy Q A, IsPesOptimal B πp → ∀ p : Q,
      (∃ α : A, ((⨅ M : Member B, VIact M.1 α (lowerV B πp) p),
          (⨆ M : Member B, VIact M.1 α (upperV B πp) p)) = intervalV B πp p) ∧
      ∀ α : A, pesLE ((⨅ M : Member B, VIact M.1 α (lowerV B πp) p),
          (⨆ M : Member B, VIact M.1 α (upperV B πp) p)) (intervalV B πp p)) := by sorry

end BoundedParamMDP.Optimal
