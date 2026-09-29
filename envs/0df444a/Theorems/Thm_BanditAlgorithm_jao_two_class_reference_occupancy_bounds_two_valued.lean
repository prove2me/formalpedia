-- Prove2me | Theorems.Thm_BanditAlgorithm_jao_two_class_reference_occupancy_bounds_two_valued
-- name    : BanditAlgorithm.jao_two_class_reference_occupancy_bounds_two_valued
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-06T03:20:11.778856+00:00
-- url     : https://prove2.me/theorems/a9017b89-2079-4037-bb61-5c8ef42f381f
-- title:
--   JAO equation (35) for a two-class MDP: from any initial state the reference reward and the total plays of the plantable pairs are at most $\frac{T}{2} + \frac{D'}{2}$
-- statement:
--   **The two-class planted gadget.** The MDP is given by its defining equations rather than through an auxiliary definition. The data are a class map $\rho : S \to \{0,1\}$, an *escape* map $\mathrm{up}$, a *return* map $\mathrm{down}$ and a *navigation* map $\mathrm{nav}$, and $M$ satisfies: the reward is the class, $r(s,b) = \rho(s)$; from a class-$0$ state $s$ every action $b$ goes to the class-$1$ state $\mathrm{up}(s)$ with probability $\delta + \varepsilon\,[\,(s,b) = (s^*,b^*)\,]$ and to the class-$0$ state $\mathrm{nav}(s,b)$ otherwise; from a class-$1$ state $s$ every action goes to the class-$0$ state $\mathrm{down}(s)$ with probability $\delta$ and stays at $s$ otherwise. Every row is supported on two distinct states whose masses sum to $1$, so the transition function is pinned down completely. The reference MDP $M_0$ is the same shape with $\varepsilon = 0$. For $S = 2$ and $\rho = \mathrm{id}$ this is JAO Figure 3 with $D' = 1/\delta$; for $S > 2$ it is the composite of Figure 4, its class-$0$ states being the $s_\circ^{(i)}$.
--
--   The whole of JAO Section 6 is run at this level of generality, on the composite MDP itself rather than on the collapsed two-state MDP they pass to on p. 1583. That reduction is not available as an inequality between regrets: the simulating policy would have to be produced before the planting is chosen, and it sees neither which copy the composite is in nor which of the $A$ actions was played. Working with the class in place of the state avoids it, and no step of the argument is lost.
--
--   Throughout, the initial state $s_0$ is arbitrary and of either class.
--
--   **On the two-valuedness hypothesis.** The statement carries $\forall s,\ \rho(s) \in \{0,1\}$ explicitly. It is not decoration: the row equations above only constrain states of class $0$ and of class $1$, so without it a state of neither class has a completely unconstrained transition row and an arbitrarily large reward, and the conclusion fails outright from such an initial state. An earlier version of this node omitted it and has been deprecated.
--
--   **Statement.** For $0 < \delta \le \tfrac13$, every horizon $T$, **every** policy $\pi$ and every initial state $s_0$, in the reference MDP
--   $$\mathbb{E}_{\mathrm{unif}}\bigl[\text{reward}\bigr] \le \frac{T}{2} + \frac{1}{2\delta}
--   \qquad\text{and}\qquad
--   \sum_{i=1}^{m} \mathbb{E}_{\mathrm{unif}}\bigl[N_{\mathrm{arm}(i)}\bigr] \le \frac{T}{2} + \frac{1}{2\delta},$$
--   where $\mathrm{arm}$ is any injection of $m$ plantable pairs into the class-$0$ state-action pairs.
--
--   This is equation (35) of JAO (p. 1583) with $D' = 1/\delta$, in the direction the assembly needs. In the reference MDP all actions have the same transition law, so the policy is irrelevant and the class process is the two-state chain with both crossing probabilities equal to $\delta$: writing $W_0(n)$ for the probability that round $n+1$ has class $1$, the recursion $W_0(n+1) = \delta + (1-2\delta)W_0(n)$ solves to $W_0(n) = \tfrac12 + (\rho(s_0) - \tfrac12)(1-2\delta)^n$. Summing the geometric remainder gives $\sum_{n<T} W_0(n) \le \tfrac{T}{2} + \tfrac{1}{4\delta}$ from either class, which is the first bound.
--
--   The second is the consequence JAO record just after (37). The pairs $\mathrm{arm}(i)$ are distinct and all lie at class-$0$ states, so the counts $N_{\mathrm{arm}(i)}$ are supported on disjoint events and their sum is at most the number of rounds spent in class $0$, whose expectation is $T - \sum_{n<T} W_0(n) \le \tfrac{T}{2} + \tfrac{1}{4\delta}$. Injectivity of $\mathrm{arm}$ is exactly what makes the counts disjoint, and it is why the plantable pairs may be spread over many states without the bound degrading — this is the point at which the composite MDP behaves like a $m$-armed bandit rather than an $A'$-armed one.
-- source:
--   Jaksch, Ortner & Auer, "Near-optimal Regret Bounds for Reinforcement Learning", JMLR 11 (2010) 1563-1600, Section 6 (pp. 1583-1586): equations (34)-(37), Lemma 13 and the optimal-gain computation. Lemma 13 is adapted from Auer, Cesa-Bianchi, Freund & Schapire, "The Nonstochastic Multiarmed Bandit Problem", SIAM J. Comput. 32 (2002) 48-77, Theorem A.2.

import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_UCRL2ConfidenceSets

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.jao_two_class_reference_occupancy_bounds_two_valued {S A m : ℕ}
    (δ : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 3)
    (ρ : Fin S → ℝ) (up down : Fin S → Fin S) (nav : Fin S → Fin A → Fin S)
    (hρ01 : ∀ s, ρ s = 0 ∨ ρ s = 1)
    (arm : Fin m → Fin S × Fin A) (harm : Function.Injective arm)
    (harm0 : ∀ i, ρ (arm i).1 = 0) (M₀ : FiniteMDP S A)
    (hrM₀ : ∀ s b, M₀.r s b = ρ s)
    (hrow0M₀ : ∀ s b, ρ s = 0 →
        ρ (up s) = 1 ∧ ρ (nav s b) = 0 ∧ up s ≠ nav s b ∧
        (M₀.P s b (up s) : ℝ) = δ ∧
        (M₀.P s b (nav s b) : ℝ) = 1 - δ)
    (hrow1M₀ : ∀ s b, ρ s = 1 →
        ρ (down s) = 0 ∧ down s ≠ s ∧
        (M₀.P s b (down s) : ℝ) = δ ∧ (M₀.P s b s : ℝ) = 1 - δ)
    (T : ℕ) (π : MDPPolicy S A) (s₀ : Fin S) :
    (∫ h, mdpTrajectoryReward M₀ h ∂(mdpMeasure M₀ (mdpStateDirac s₀) π T))
        ≤ (T : ℝ) / 2 + 1 / (2 * δ)
      ∧ ∑ i : Fin m,
            (∫ h, (mdpVisitCount h T (arm i).1 (arm i).2 : ℝ)
              ∂(mdpMeasure M₀ (mdpStateDirac s₀) π T))
          ≤ (T : ℝ) / 2 + 1 / (2 * δ) := by
  sorry
