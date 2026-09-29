-- Prove2me | Theorems.Thm_BanditAlgorithm_jao_planted_two_class_mdp_regret_core_per_initial_state
-- name    : BanditAlgorithm.jao_planted_two_class_mdp_regret_core_per_initial_state
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-06T03:06:31.353794+00:00
-- url     : https://prove2.me/theorems/37e62c8e-d846-45c5-924a-bf5a1e9c4506
-- title:
--   JAO Section 6, equations (34)-(37) and Lemma 13, run directly on a two-class MDP with $m$ plantable actions: regret $\Omega(\sqrt{mT/\delta})$ from a given initial state
-- statement:
--   **The two-class planted gadget.** The MDP is described by its defining equations rather than through an auxiliary definition. The data are a class map $\rho : S \to \{0,1\}$, an *escape* map $\mathrm{up}$, a *return* map $\mathrm{down}$ and a *navigation* map $\mathrm{nav}$, and the MDP $M$ satisfies
--
--   * the reward is the class, $r(s,b) = \rho(s)$ for every action $b$;
--   * from a class-$0$ state $s$ every action $b$ goes to the class-$1$ state $\mathrm{up}(s)$ with probability $\delta + \varepsilon\,[\,(s,b) = (s^*,b^*)\,]$ and to the class-$0$ state $\mathrm{nav}(s,b)$ otherwise;
--   * from a class-$1$ state $s$ every action goes to the class-$0$ state $\mathrm{down}(s)$ with probability $\delta$ and stays at $s$ otherwise.
--
--   Each row is supported on two states and the two masses sum to $1$, so these equations pin the transition function down completely. For $\varepsilon = 0$ this is the reference MDP $M_0$; for the planting at $(s^*, b^*)$ it is $M$. When $S = 2$ and $\rho = \mathrm{id}$ this is the gadget of JAO Figure 3 with $D' = 1/\delta$; for $S > 2$ it is the composite MDP of Figure 4, whose class-$0$ states are the $s_\circ^{(i)}$ and whose navigation map moves between the copies.
--
--   **Statement.** There is a universal $c > 0$ with the following property. Let $m \ge 20$, $0 < \delta \le \tfrac13$ and $16m \le \delta T$, and set $\varepsilon = \tfrac15\sqrt{\delta m/T}$. Suppose given a two-class gadget shape on $S$ states and $A$ actions together with an injection $\mathrm{arm} : \{1,\dots,m\} \to S \times A$ whose image consists of class-$0$ pairs, each of which is a fixed point of the navigation map and whose state satisfies $\mathrm{down}(\mathrm{up}(s)) = s$. Let $M_0$ be the reference MDP and $M_i$ the MDP planted at $\mathrm{arm}(i)$. Then for every learning algorithm $\pi$ **and every initial state $s_0$** there is a planting $i$ with
--   $$\mathbb{E}\bigl[\Delta(M_i, \pi, s_0, T)\bigr] \;\ge\; c\,\sqrt{Tm/\delta}.$$
--
--   The planting is chosen after the initial state, which is what makes the statement true; see the discussion of the quantifier on the parent. The initial state is otherwise unrestricted -- it may have either class.
--
--   **Why not reduce to the two-state gadget.** JAO argue the composite by reducing it to the collapsed MDP in which all $s_\circ^{(i)}$ are identified (p. 1583, "Note that learning this MDP is easier"). That is an intuition they never make precise, and the natural precise version -- an inequality between the two regrets -- is not available: the simulating policy for the collapsed MDP would have to be produced from the composite's policy *before* the planting is chosen, and it observes neither which copy the composite is in nor which of the $A$ actions was played, both of which the composite's policy uses. This statement keeps the argument on the composite itself, where every step of Section 6 goes through unchanged.
--
--   **Proof.** Write $W(n)$ for the probability that the state of round $n+1$ has class $1$. Conditioning on one step gives $W(n+1) = \delta + (1-2\delta)W(n) + \varepsilon\,Q(n)$, where $Q(n)$ is the probability that round $n+1$ plays the planted pair, and the reward is $\sum_{n<T} W(n)$. Comparing with the reference recursion $W_0(n+1) = \delta + (1-2\delta)W_0(n)$ started at the same $W_0(0) = \rho(s_0)$, the difference $d(n) = W(n) - W_0(n)$ obeys $d(0) = 0$ and $d(n+1) = (1-2\delta)d(n) + \varepsilon Q(n)$, which telescopes on summation to $2\delta\sum_{n<T} d(n) \le \varepsilon\sum_{n<T} Q(n)$; this is equation (34), and unlike JAO's version it needs no stochastic-domination coupling. The reference recursion is solved explicitly, giving $\sum_{n<T} W_0(n) \le \tfrac T2 + \tfrac1{4\delta}$ from either class, which is equation (35). Since $\mathrm{arm}$ is injective and lands in class-$0$ pairs, the counts $N_{\mathrm{arm}(i)}$ are disjoint and bounded by the time spent in class $0$, so their reference expectations sum to at most $\tfrac T2 + \tfrac1{2\delta}$. The planted and reference MDPs differ in exactly one row, and both rows are two-point with masses $\delta$ and $\delta+\varepsilon$, so the divergence decomposition with the Bernoulli relative entropy and Pinsker's inequality give Lemma 13. The optimal gain is at least $\frac{\delta+\varepsilon}{2\delta+\varepsilon}$ because the planted pair is a navigation fixed point, so always playing it from the planted state reproduces the two-state gadget. Averaging over the $m$ plantings and choosing $\varepsilon = \tfrac15\sqrt{\delta m/T}$ leaves a positive multiple of $\sqrt{Tm/\delta}$.
-- source:
--   Jaksch, Ortner & Auer, "Near-optimal Regret Bounds for Reinforcement Learning", JMLR 11 (2010) 1563-1600, Theorem 5 (p. 1581) and Section 6 (pp. 1582-1586). Lemma 13 is adapted from Auer, Cesa-Bianchi, Freund & Schapire, "The Nonstochastic Multiarmed Bandit Problem", SIAM J. Comput. 32 (2002) 48-77, Theorem A.2.

import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_FiniteMDPLearning

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.jao_planted_two_class_mdp_regret_core_per_initial_state :
    ∃ c : ℝ, 0 < c ∧
      ∀ (S A m : ℕ), 20 ≤ m → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 3 →
        ∀ T : ℕ, (16 : ℝ) * m ≤ δ * T →
          ∀ ε : ℝ, ε = 1 / 5 * Real.sqrt (δ * m / T) →
            ∀ (ρ : Fin S → ℝ) (up down : Fin S → Fin S) (nav : Fin S → Fin A → Fin S)
              (arm : Fin m → Fin S × Fin A)
              (M : Fin m → FiniteMDP S A) (M₀ : FiniteMDP S A),
              Function.Injective arm →
              (∀ i, ρ (arm i).1 = 0) →
              (∀ i, nav (arm i).1 (arm i).2 = (arm i).1) →
              (∀ i, down (up (arm i).1) = (arm i).1) →
              (∀ s, ρ s = 0 ∨ ρ s = 1) →
              (∀ s b, M₀.r s b = ρ s) →
              (∀ s b, ρ s = 0 →
                  ρ (up s) = 1 ∧ ρ (nav s b) = 0 ∧ up s ≠ nav s b ∧
                  (M₀.P s b (up s) : ℝ) = δ ∧
                  (M₀.P s b (nav s b) : ℝ) = 1 - δ) →
              (∀ s b, ρ s = 1 →
                  ρ (down s) = 0 ∧ down s ≠ s ∧
                  (M₀.P s b (down s) : ℝ) = δ ∧
                  (M₀.P s b s : ℝ) = 1 - δ) →
              (∀ i, ∀ s b, (M i).r s b = ρ s) →
              (∀ i, ∀ s b, ρ s = 0 →
                  ((M i).P s b (up s) : ℝ)
                      = δ + (if (s, b) = arm i then ε else 0) ∧
                  ((M i).P s b (nav s b) : ℝ)
                      = 1 - δ - (if (s, b) = arm i then ε else 0)) →
              (∀ i, ∀ s b, ρ s = 1 →
                  ((M i).P s b (down s) : ℝ) = δ ∧
                  ((M i).P s b s : ℝ) = 1 - δ) →
              ∀ π : MDPPolicy S A, ∀ s₀ : Fin S,
                ∃ i : Fin m,
                  c * Real.sqrt ((T : ℝ) * m / δ) ≤
                    ∫ h, mdpRegret (M i) T h
                      ∂(mdpMeasure (M i) (mdpStateDirac s₀) π T) := by
  sorry
