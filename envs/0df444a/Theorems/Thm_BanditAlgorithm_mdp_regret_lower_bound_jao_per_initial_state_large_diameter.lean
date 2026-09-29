-- Prove2me | Theorems.Thm_BanditAlgorithm_mdp_regret_lower_bound_jao_per_initial_state_large_diameter
-- name    : BanditAlgorithm.mdp_regret_lower_bound_jao_per_initial_state_large_diameter
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-06T03:06:12.465632+00:00
-- url     : https://prove2.me/theorems/10d73793-7a4f-4608-900c-89d1e1d4c917
-- title:
--   JAO Theorem 5 per initial state, large-diameter regime $D \ge 12$
-- statement:
--   The regime $D \ge 12$, i.e. $\delta = 4/D \le \tfrac13$, of the per-initial-state form of JAO Theorem 5. This is the main construction of Section 6: $\lfloor S/2\rfloor$ copies of the two-state gadget of Figure 3 with escape probability $\delta$, one of them carrying a planted action with escape probability $\delta + \varepsilon$, joined into a single MDP of diameter at most $D$.
--
--   The complementary regime $D < 12$ is JAO's footnote 11 and is a different instance.
--
--   **On the quantifier.** JAO Theorem 5 reads "there is an MDP $M$ with $S$ states, $A$ actions, and diameter $D$, such that **for any initial state** $s \in S$ the expected regret ... is $\ge 0.015\sqrt{DSAT}$", i.e. $\exists M\,\forall s$. Section 6 proves something weaker: on p. 1583 it says "we will consider the simpler MDP where all $s_\circ$-states are identified. **We set this state to be the initial state**", and the argument never leaves that state. The two readings are genuinely different, and JAO's construction cannot support the stronger one: let $\pi_0$ read the initial state, let $i$ be its copy, and never leave copy $i$, running a minimax-optimal bandit algorithm over that copy's $A'$ gadget actions. Staying is possible, since the gadget actions at $s_\circ^{(i)}$ lead to $s_p^{(i)}$ or stay and $s_p^{(i)}$ returns; and the global optimal gain $\frac{\delta+\varepsilon}{2\delta+\varepsilon}$ is attainable inside a single copy. So from $s_\circ^{(i^*)}$, $\pi_0$ faces exactly the two-state gadget with $A'$ arms and suffers only $\Theta(\sqrt{TA'/\delta})$, a factor $\asymp\sqrt{k}$ below $\sqrt{TkA'/\delta} \asymp \sqrt{DSAT}$. Whichever copy carries the planted action, the initial state in *that* copy is the cheap one.
--
--   Nor is it a matter of bookkeeping: the argument needs a plantable action that the reference algorithm plays rarely, and averaging over the $m$ actions gives $\frac1m(\frac T2 + \frac1{2\delta})$ for a fixed start but only $\frac Sm(\cdots)$ for one action good at all $S$ starts simultaneously, which turns $\sqrt{DSAT}$ into $\sqrt{DAT}$.
--
--   This node therefore states the per-initial-state form, $\forall s\,\exists M$: the hard MDP may depend on the initial state, which costs nothing, since the construction is simply relabelled so that $s$ plays the role of $s_\circ$. That is the standard reading of "for any initial state there is a hard MDP", it is exactly what Section 6 establishes, and it is what the $\tilde O(DS\sqrt{AT})$ upper bound of the same paper is compared against. Note that the stronger $\exists M\,\forall s$ form is **not** known to be false: it quantifies existentially over MDPs, and refuting it would mean showing that *every* MDP with these parameters admits a cheap initial state. Camping is cheap only because JAO's optimal gain lives inside one copy; an MDP whose optimal gain needs correct actions at many states, or one that mixes in $O(D)$ steps, could plausibly satisfy it. Only the route through this construction is closed.
-- source:
--   Jaksch, Ortner & Auer, "Near-optimal Regret Bounds for Reinforcement Learning", JMLR 11 (2010) 1563-1600, Theorem 5 (p. 1581) and Section 6 (pp. 1582-1586). Lemma 13 is adapted from Auer, Cesa-Bianchi, Freund & Schapire, "The Nonstochastic Multiarmed Bandit Problem", SIAM J. Comput. 32 (2002) 48-77, Theorem A.2.

import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_FiniteMDPLearning

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.mdp_regret_lower_bound_jao_per_initial_state_large_diameter :
    ∃ C : ℝ, 0 < C ∧
      ∀ S A T : ℕ, ∀ D : ℝ, 10 ≤ S → 10 ≤ A →
        20 * (Real.log S / Real.log A) ≤ D → D * S * A ≤ (T : ℝ) → 12 ≤ D →
          ∀ π : MDPPolicy S A, ∀ s : Fin S,
            ∃ M : FiniteMDP S A,
              mdpDiameterENN M ≤ ENNReal.ofReal D ∧
              C * Real.sqrt (D * S * A * T) ≤
                ∫ h, mdpRegret M T h ∂(mdpMeasure M (mdpStateDirac s) π T) := by
  sorry
