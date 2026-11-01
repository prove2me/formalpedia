-- Prove2me | Theorems.Thm_AggStatePG_bellman_contraction_fixed_point
-- name    : AggStatePG.bellman_contraction_fixed_point
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:43:55.982884+00:00
-- url     : https://prove2.me/theorems/beebaab8-0547-419b-bb31-82e7eb1f3b0a
-- title:
--   p.5: $T$ and $T_\pi$ are $\gamma$-contractions and $V^*$ is the unique fixed point of $T$ (the $V_\pi$ part: referenced bellman_equations)
-- statement:
--   Throughout, $M=(\mathcal S,\mathcal A,r,P,\gamma,\rho)$ is a finite Markov decision process: finite state and action sets, a real reward $r(s,a)$ (no bound), transition probabilities $P(s'\mid s,a)$, a discount factor $\gamma\in(0,1)$ and an initial distribution $\rho$ on $\mathcal S$. $\Pi$ is the set of stationary randomized policies $\pi:\mathcal S\to\Delta(\mathcal A)$, $V_\pi$ the value function of $\pi$, $Q_\pi(s,a)=r(s,a)+\gamma\sum_{s'}P(s'\mid s,a)V_\pi(s')$, $V^*(s)=\max_{\pi\in\Pi}V_\pi(s)$, $J(\pi)=(1-\gamma)\sum_s\rho(s)V_\pi(s)$ and $\eta_\pi=(1-\gamma)\sum_{t\ge0}\gamma^t\rho P_\pi^t$ the discounted state occupancy measure.
--
--   1. $T$ is a contraction with modulus $\gamma$ in the maximum norm: $\|TV-TW\|_\infty\le\gamma\|V-W\|_\infty$ for all $V,W\in\mathbb R^{\mathcal S}$;
--   2. for every policy $\pi\in\Pi$, $T_\pi$ is a contraction with modulus $\gamma$ in the maximum norm;
--   3. $TV^*=V^*$;
--   4. every fixed point of $T$ equals $V^*$.
--
--   Together with the fact that $V_\pi$ is the unique fixed point of $T_\pi$ (the referenced Proved theorems `FoundationsML.ReinforcementLearning.bellman_equations` and `bellman_equations_unique_solution`), this is the sentence "It is well known that $T$ and $T_\pi$ are contraction mappings with respect the maximum norm. Their unique fixed points are $V^*$ and $V_\pi$, respectively." It is what turns the element-wise inequality $V\succeq TV-ce$ into a bound against $V^*$ at the end of the proof of Theorem 3.
--
--   **Formalization Note** $V^*$ is the supremum of the policy values, not an assumed fixed point. The norm on $\mathbb R^{\mathcal S}$ is Mathlib's sup norm.
--
--   Differences from the source:
--   - encoding: finite action space A = {1, …, |A|} → a finite nonempty action type ([Nonempty A]); reason: Δ(A) and Π are empty for an empty action set; the paper's MDP has policies (an optimal one exists, p.4)
--   - encoding: V*(s) = max_{π∈Π} V_π(s) → Vstar = sSup of {V_π(s) : π ∈ Π}; reason: the set is bounded and the maximum is attained (an optimal policy exists, p.4), so sSup is the maximum
--   - encoding: TV(s) = max_{d∈Δ(A)} [r(s,d) + γ Σ_{s′} P(s′|s,d)V(s′)] → bellmanOpt = sSup of the image of Δ(A); reason: for nonempty finite A the image is a nonempty compact set, so sSup is the maximum
-- source:
--   Russo, Approximation Benefits of Policy Gradient Methods with Aggregated States, arXiv:2007.11684v3, §2, p.5 (contraction and fixed points of T and T_π)

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_AggStatePG_bellmanPol
import Definitions.Def_AggStatePG_bellmanOpt
import Definitions.Def_AggStatePG_Vstar

open FoundationsML.ReinforcementLearning

namespace AggStatePG

/-- **Contraction and fixed points** (Russo, *Approximation Benefits of Policy Gradient Methods with Aggregated States*, arXiv:2007.11684v3, §2, p.5): "It is well known that `T` and `T_π` are
contraction mappings with respect the maximum norm. Their unique fixed points are `V*` and `V_π`,
respectively." This item states:
1. `T` is a `γ`-contraction in the maximum norm: `‖TV - TW‖_∞ ≤ γ ‖V - W‖_∞`;
2. for every policy `π ∈ Π`, `T_π` is a `γ`-contraction in the maximum norm;
3. `V* = max_π V_π` is a fixed point of `T`: `TV* = V*`;
4. `V*` is the only fixed point of `T`.
(That `V_π` is the unique fixed point of `T_π` is the published Proposition 17.9/Theorem 17.10 of
Mohri et al., `FoundationsML.ReinforcementLearning.bellman_equations` and
`bellman_equations_unique_solution`.)

**Formalization Note.** `‖·‖` on `S → ℝ` is Mathlib's sup norm, the paper's `‖·‖_∞`. `V*` is
`Vstar` (the supremum over all policies), not an assumed fixed point. The action type is nonempty. -/
theorem bellman_contraction_fixed_point {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    [Nonempty A] (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (r : S → A → ℝ)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    (∀ V W : S → ℝ, ‖bellmanOpt P r γ V - bellmanOpt P r γ W‖ ≤ γ * ‖V - W‖) ∧
    (∀ π : S → A → ℝ, IsPolicy π → ∀ V W : S → ℝ,
        ‖bellmanPol π P r γ V - bellmanPol π P r γ W‖ ≤ γ * ‖V - W‖) ∧
    bellmanOpt P r γ (Vstar P r γ) = Vstar P r γ ∧
    (∀ V : S → ℝ, bellmanOpt P r γ V = V → V = Vstar P r γ) := by sorry

end AggStatePG
