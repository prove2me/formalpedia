-- Prove2me | Theorems.Thm_BanditAlgorithm_mdp_regret_lower_bound_jao_universal_constant_large_diameter
-- name    : BanditAlgorithm.mdp_regret_lower_bound_jao_universal_constant_large_diameter
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-05T16:55:28.863627+00:00
-- url     : https://prove2.me/theorems/a86f4f0c-bb57-4cb7-bc79-2ab7a598566a
-- title:
--   JAO Theorem 5, main regime $D \ge 12$ (so $\delta = 4/D \le 1/3$)
-- statement:
--   For any learning algorithm and any $S, A \ge 10$, $D \ge 20\log_A S$ and $T \ge DSA$, there is an MDP with $S$ states, $A$ actions and diameter at most $D$ on which, from **every** initial state, the expected regret after $T$ steps is at least $C\sqrt{DSAT}$ for a universal constant $C > 0$.
--
--   This is Theorem 5 of Jaksch, Ortner and Auer (2010), the matching lower bound for their $\tilde{O}(D S \sqrt{AT})$ UCRL2 upper bound, stated with the hypotheses of the original paper. Those hypotheses are not cosmetic: the construction places $k = \lfloor S/2 \rfloor$ copies of a two-state gadget with $A' = \lfloor (A-1)/2 \rfloor$ actions each, connected by $A'+1$ further actions per state inducing an $A'$-ary tree on the reward-$0$ states, so it simply does not exist unless $A$ is large enough to supply $2A'+1$ actions, and the final constant needs $kA' \ge 20$.
--
--   This is the **main regime** $D \ge 12$, equivalently $\delta = 4/D \le 1/3$, which is the standing assumption of the construction (JAO p. 1582).
--
--   **Proof sketch (JAO Section 6).** The hard instance is a two-state gadget: a state $s_\circ$ with reward $0$ and a state $s_p$ with reward $1$, with $A'$ actions, where $p(s_p \mid s_\circ, a) = \delta := 4/D$ for every action except a single good action $a^*$ for which it is $\delta + \varepsilon$, and $p(s_\circ \mid s_p, a) = \delta$ throughout. Its diameter is $D' = 1/\delta = D/4$. One takes $k$ copies, exactly one of which carries a good action, and joins them into a single MDP of diameter at most $2(D/4 + \lceil \log_{A'} k \rceil) \le D$.
--
--   The analysis then **identifies all $s_\circ$-states**, collapsing the composite MDP to a two-state MDP $M'$ with $kA'$ actions. Learning $M'$ is easier (the learner may switch between copies for free) and its optimal average reward $(\delta+\varepsilon)/(2\delta+\varepsilon)$ is unchanged, so a lower bound for $M'$ transfers. On $M'$ the argument is the multi-armed bandit lower bound of Auer et al. (2002b): equations (34)-(37) bound $\mathbb{E}_a[R(M')]$ by $T/2 + \mathbb{E}_a[N_\circ^*]\varepsilon D' + D'/2$, Lemma 13 (a Pinsker-type bound on state sequences) controls $\mathbb{E}_a[N_\circ^*]$, and the choice $\varepsilon := \tfrac15\sqrt{kA'D'/T}$ makes the average over a uniformly random planted pair exceed a constant multiple of $\sqrt{D'kA'T}$.
--
--   Note that the tree never enters the analysis, which is why this proof avoids the difficulty in the Lattimore-Szepesvari exposition (Theorem 38.7), where a tree "of minimum depth" leaves the leaves at two different depths and Claim 38.11 fails for large $T$.
--
--   **On the constant.** The paper displays Theorem 5 with the explicit constant $0.015$ on $\sqrt{DSAT}$, but its own proof in Section 6 does not deliver that. The final line of Section 6 (p. 1586) reads
--   $$\mathbb{E}^*\!\left[\Delta(M', \mathfrak{A}, s, T)\right] > 0.015\sqrt{D'kA'T},$$
--   in terms of the *gadget* parameters $D' = D/4$, $k = \lfloor S/2 \rfloor$ and $A' = \lfloor (A-1)/2 \rfloor$, and the substitution $D'kA' \to DSA$ is never justified. It is in fact false: the composite MDP must fit in $S$ states and $A$ actions, which forces $2k \le S$ and $2A' + 1 \le A$, hence
--   $$D'kA' \;=\; \tfrac{D}{4}\,k\,A' \;\le\; \tfrac{DSA}{16},$$
--   so $0.015\sqrt{D'kA'T} \le 0.0039\sqrt{DSAT}$ under any rounding convention. Minimising $\tfrac14\cdot\tfrac{\lfloor S/2\rfloor}{S}\cdot\tfrac{\lfloor (A-1)/2\rfloor}{A}$ over $S, A \ge 10$ gives $1/22$ at $(S,A) = (11,10)$, so the largest constant the argument can yield on $\sqrt{DSAT}$ is $0.015/\sqrt{22} = 0.00320$.
--
--   The remaining arithmetic of Section 6 is correct: recomputing the bracket in the penultimate display at $kA' = 20$ (the minimum permitted by $S, A \ge 10$) gives $0.016660 > 0.015$, exactly as claimed. The error is the single unstated substitution at the end.
--
--   A second, smaller loss is that Section 6 proves the bound for the initial state $s_\circ$, while Theorem 5 asserts it for *every* initial state; transferring costs a further additive $O(D')$, of which the proof has already spent one copy ($D'/2$) of its bracket. For these reasons this node states a universal but unspecified constant $C > 0$ — the form in which the result is universally cited, and the form used by Lattimore and Szepesvari (Bandit Algorithms, Theorem 38.7). A witness $C = 0.0008$ is comfortably supported by Section 6.
-- source:
--   Jaksch, Ortner & Auer, "Near-optimal Regret Bounds for Reinforcement Learning", JMLR 11 (2010) 1563-1600, Theorem 5 (p. 1567) and its proof in Section 6 (pp. 1582-1586).

import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_FiniteMDPLearning

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.mdp_regret_lower_bound_jao_universal_constant_large_diameter :
    ∃ C : ℝ, 0 < C ∧
      ∀ S A T : ℕ, ∀ D : ℝ, 10 ≤ S → 10 ≤ A →
        20 * (Real.log S / Real.log A) ≤ D → D * S * A ≤ (T : ℝ) → 12 ≤ D →
          ∀ π : MDPPolicy S A,
            ∃ M : FiniteMDP S A,
              mdpDiameterENN M ≤ ENNReal.ofReal D ∧
              ∀ s : Fin S,
                C * Real.sqrt (D * S * A * T) ≤
                  ∫ h, mdpRegret M T h ∂(mdpMeasure M (mdpStateDirac s) π T) := by
  sorry
