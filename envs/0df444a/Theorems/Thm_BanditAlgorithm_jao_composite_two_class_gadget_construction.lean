-- Prove2me | Theorems.Thm_BanditAlgorithm_jao_composite_two_class_gadget_construction
-- name    : BanditAlgorithm.jao_composite_two_class_gadget_construction
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-05T19:39:57.298087+00:00
-- url     : https://prove2.me/theorems/6d284ca3-52f8-4b69-87e2-d8914ab19aae
-- title:
--   JAO Figure 4: a two-class gadget on $S$ states and $A$ actions with $\lfloor S/2\rfloor\lfloor A/2\rfloor$ plantable actions and diameter $\le D$
-- statement:
--   **The two-class planted gadget.** Both children speak about the same class of MDPs, described by its defining equations rather than through an auxiliary definition. The data are a class map $\rho : S \to \{0,1\}$, an *escape* map $\mathrm{up}$, a *return* map $\mathrm{down}$ and a *navigation* map $\mathrm{nav}$, and the MDP $M$ satisfies
--
--   * the reward is the class, $r(s,b) = \rho(s)$ for every action $b$;
--   * from a class-$0$ state $s$ every action $b$ goes to the class-$1$ state $\mathrm{up}(s)$ with probability $\delta + \varepsilon\,[\,(s,b) = (s^*,b^*)\,]$ and to the class-$0$ state $\mathrm{nav}(s,b)$ otherwise;
--   * from a class-$1$ state $s$ every action goes to the class-$0$ state $\mathrm{down}(s)$ with probability $\delta$ and stays at $s$ otherwise.
--
--   Since each row is supported on two states and the two masses sum to $1$, these equations pin the transition function down completely. For $\varepsilon = 0$ this is the *reference* MDP $M_0$; for the planting at $(s^*,b^*)$ it is $M$. When $S = 2$, $\rho = \mathrm{id}$ and $\mathrm{nav}$ is constant, this is exactly the gadget of JAO Figure 3 with $D' = 1/\delta$; for $S > 2$ it is the composite MDP of Figure 4, whose class-$0$ states are the $s_\circ^{(i)}$, whose class-$1$ states are the $s_p^{(i)}$, and whose navigation map moves between the copies.
--
--   **Statement.** Let $S, A \ge 10$ and $D \ge 12$ with $D \ge 20\log_A S$, and let $0 \le \varepsilon \le \tfrac{1}{5D}$. Then there is a two-class gadget shape on $S$ states and $A$ actions with $\delta = 4/D$, an injection $\mathrm{arm}$ of $m = \lfloor S/2\rfloor\lfloor A/2\rfloor$ class-$0$ pairs that are navigation fixed points and satisfy $\mathrm{down}(\mathrm{up}(s)) = s$, a reference MDP and, for each planting, a planted MDP, such that **every planted MDP has diameter at most $D$**.
--
--   This is the construction of JAO Figure 4 (p. 1582), with one simplification. JAO give each state $A' + 1$ extra actions inducing an $A'$-ary tree on the reward-$0$ states, separate from the $A'$ bandit actions. Here every action gambles: from a class-$0$ state each of the $A$ actions escapes to that copy's class-$1$ state with probability $\delta$ (or $\delta + \varepsilon$ for the planted pair) and otherwise moves along the navigation graph. The first $\lfloor A/2 \rfloor$ actions are navigation fixed points and are the plantable ones; the remaining $\lceil A/2\rceil \ge 5$ actions drive an expander-free routing graph on the $\lceil S/2\rceil$ class-$0$ states. This keeps every transition row two-point, which is what makes the relative entropy of a planting Bernoulli, and it costs nothing: $m = \lfloor S/2\rfloor\lfloor A/2\rfloor \ge \tfrac{25}{121}SA$, better than the $\lfloor S/2\rfloor\lfloor (A-1)/2\rfloor$ of the paper.
--
--   **The diameter.** Fix a target and let $L$ be the routing depth, so that a memoryless deterministic policy reaches the target copy in at most $L$ navigation steps. Bound the expected hitting time by a Foster-Lyapunov drift function: from a class-$1$ state one waits a $\mathrm{Geom}(\delta)$ time to return, from a class-$0$ state one advances one navigation step per round unless one escapes, in which case one returns to the *same* copy and resumes, and once at the target copy one waits a $\mathrm{Geom}(\delta)$ time to escape into it. The function $g(s) = 3\,\mathrm{dist}(s) + \tfrac{1}{\delta}\,[\text{class } 1]$ (plus $\tfrac1\delta$ throughout when the target has class $1$) has drift $\le -1$ off the target because $\delta \le \tfrac13$, giving an expected hitting time at most $\tfrac{2}{\delta} + 3L = \tfrac{D}{2} + 3L$. So it suffices that $L \le D/6$, and taking $L = \lfloor D/6 \rfloor \ge 2$ the routing graph on $\lceil S/2 \rceil$ nodes with out-degree $\lceil A/2\rceil$ has depth $\le L$: this is where $D \ge 20\log_A S$ is used, and it holds with room to spare, the binding case being $\lceil S/2\rceil \le \lceil A/2\rceil^2$ when $D$ is near $12$.
-- source:
--   Jaksch, Ortner & Auer, "Near-optimal Regret Bounds for Reinforcement Learning", JMLR 11 (2010) 1563-1600, Section 6 (pp. 1582-1586): the construction of Figures 3-4, equations (34)-(37) and Lemma 13. Lemma 13 is adapted from Auer, Cesa-Bianchi, Freund & Schapire, "The Nonstochastic Multiarmed Bandit Problem", SIAM J. Comput. 32 (2002) 48-77, Theorem A.2.

import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_FiniteMDPLearning

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.jao_composite_two_class_gadget_construction :
    ∀ S A : ℕ, 10 ≤ S → 10 ≤ A → ∀ D : ℝ, 12 ≤ D →
      20 * (Real.log S / Real.log A) ≤ D →
        ∀ ε : ℝ, 0 ≤ ε → 20 * ε ≤ 4 / D →
          ∃ (ρ : Fin S → ℝ) (up down : Fin S → Fin S) (nav : Fin S → Fin A → Fin S)
            (arm : Fin (S / 2 * (A / 2)) → Fin S × Fin A)
            (M : Fin (S / 2 * (A / 2)) → FiniteMDP S A) (M₀ : FiniteMDP S A),
            Function.Injective arm ∧
            (∀ i, ρ (arm i).1 = 0) ∧
            (∀ i, nav (arm i).1 (arm i).2 = (arm i).1) ∧
            (∀ i, down (up (arm i).1) = (arm i).1) ∧
            (∀ s, ρ s = 0 ∨ ρ s = 1) ∧
            (∀ s b, M₀.r s b = ρ s) ∧
            (∀ s b, ρ s = 0 →
                ρ (up s) = 1 ∧ ρ (nav s b) = 0 ∧ up s ≠ nav s b ∧
                (M₀.P s b (up s) : ℝ) = 4 / D ∧
                (M₀.P s b (nav s b) : ℝ) = 1 - 4 / D) ∧
            (∀ s b, ρ s = 1 →
                ρ (down s) = 0 ∧ down s ≠ s ∧
                (M₀.P s b (down s) : ℝ) = 4 / D ∧
                (M₀.P s b s : ℝ) = 1 - 4 / D) ∧
            (∀ i, ∀ s b, (M i).r s b = ρ s) ∧
            (∀ i, ∀ s b, ρ s = 0 →
                ((M i).P s b (up s) : ℝ)
                    = 4 / D + (if (s, b) = arm i then ε else 0) ∧
                ((M i).P s b (nav s b) : ℝ)
                    = 1 - 4 / D - (if (s, b) = arm i then ε else 0)) ∧
            (∀ i, ∀ s b, ρ s = 1 →
                ((M i).P s b (down s) : ℝ) = 4 / D ∧
                ((M i).P s b s : ℝ) = 1 - 4 / D) ∧
            (∀ i, mdpDiameterENN (M i) ≤ ENNReal.ofReal D) := by
  sorry
