-- Prove2me | Theorems.Thm_BanditAlgorithm_mdp_regret_lower_bound_jao_large_diameter
-- name    : BanditAlgorithm.mdp_regret_lower_bound_jao_large_diameter
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-05T15:46:55.368118+00:00
-- url     : https://prove2.me/theorems/d8a518ed-7204-4989-9e89-ef9103f38fcc
-- title:
--   JAO Theorem 5, main regime $D \ge 12$ (so $\delta = 4/D \le 1/3$)
-- statement:
--   For any algorithm and any $S, A \ge 10$, $D \ge 20\log_A S$ and $T \ge DSA$, there is an MDP with $S$ states, $A$ actions and diameter at most $D$ on which, from **every** initial state, the expected regret after $T$ steps is at least $0.015\sqrt{DSAT}$.
--
--   This is the **main regime** $D \ge 12$, equivalently $\delta = 4/D \le 1/3$, which is the standing assumption of JAO's construction (p. 1582). The hard instance is built from a two-state gadget: states $s_\circ$ (reward $0$) and $s_p$ (reward $1$) with $A' = \lceil (A-1)/2 \rceil$ actions, where $p(s_p \mid s_\circ, a) = \delta := 4/D$ for every action except a single good action $a^*$ for which it is $\delta + \varepsilon$, and $p(s_\circ \mid s_p, a) = \delta$ throughout; the gadget has diameter $D' = 1/\delta = D/4$. One takes $k = \lceil S/2 \rceil$ copies, exactly one of which carries a good action, and joins them with $A'+1$ additional zero-reward actions per state inducing an $A'$-ary tree on the $s_\circ$-states, giving a composite diameter of at most $2(D/4 + \lceil \log_{A'} k \rceil) \le D$.
--
--   The analysis then identifies all $s_\circ$-states, collapsing the composite MDP to a single two-state MDP $M'$ with $kA'$ actions; learning $M'$ is easier and its optimal average reward is the same, so a lower bound for $M'$ transfers. On $M'$ the argument is the multi-armed bandit lower bound of Auer et al. (2002b): the optimal average reward is $(\delta+\varepsilon)/(2\delta+\varepsilon)$, and with $\varepsilon := \tfrac15\sqrt{kA'D'/T}$ the averaged regret over a uniformly random planted pair exceeds $0.015\sqrt{D'kA'T}$.
--
--   This is the original statement, with the explicit constant $0.015$ and the initial state universally quantified, as opposed to the Lattimore-Szepesvari restatement (Bandit Algorithms, Theorem 38.7) which asserts the bound for $S \ge 3$, $A \ge 2$ with an unspecified universal constant. The hypothesis $S, A \ge 10$ is not cosmetic: JAO's construction uses a two-state gadget with $A' = \lceil (A-1)/2 \rceil$ actions together with $A'+1$ further actions per state to connect the copies, so at $A = 2$ the construction does not exist, and the final constant is obtained from $kA' \ge 20$.
--
--   ---
--
--   **⚠ Not provable from the source as stated — see below.** The constant $0.015$ on $\sqrt{DSAT}$ does not follow from JAO Section 6. The proof ends at $0.015\sqrt{D'kA'T}$ with $D' = D/4$, $k = \lfloor S/2\rfloor$, $A' = \lfloor (A-1)/2\rfloor$; since the composite MDP must fit in $S$ states and $A$ actions, $2k \le S$ and $2A'+1 \le A$, hence $D'kA' \le DSA/16$ and the proven bound is at most $0.0039\sqrt{DSAT}$. The exact supremum over $S, A \ge 10$ is $0.015/\sqrt{22} = 0.00320$, attained at $(S,A) = (11,10)$. The rest of Section 6 is correct: its bracket at $kA' = 20$ evaluates to $0.016660 > 0.015$ as claimed. The error is a single unstated substitution $D'kA' \to DSA$ in the final line.
--
--   This node is kept only as a record of the statement as published. **Work instead on `BanditAlgorithm.mdp_regret_lower_bound_jao_universal_constant`**, which carries the same hypotheses and the same $\sqrt{DSAT}$ scaling with a universal but unspecified constant. See mission comment `afe04135` for the full computation.
-- source:
--   Thomas Jaksch, Ronald Ortner, Peter Auer, "Near-optimal Regret Bounds for Reinforcement Learning", Journal of Machine Learning Research 11 (2010) 1563-1600, Theorem 5, p. 1567; proof in Section 6 "The Lower Bound", pp. 1582-1586. Main regime delta <= 1/3 (D >= 12), the standing assumption stated on p. 1582; construction of Figures 3 and 4, the collapse on p. 1583, eqs. (34)-(37), Lemma 13, and the choice epsilon = (1/5) sqrt(k A' D'/T) on p. 1585.

import Definitions.Def_FiniteMDPLearning
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.mdp_regret_lower_bound_jao_large_diameter :
    ∀ S A T : ℕ, ∀ D : ℝ, 10 ≤ S → 10 ≤ A →
      20 * (Real.log S / Real.log A) ≤ D → D * S * A ≤ (T : ℝ) → 12 ≤ D →
        ∀ π : MDPPolicy S A,
          ∃ M : FiniteMDP S A,
            mdpDiameterENN M ≤ ENNReal.ofReal D ∧
            ∀ s : Fin S,
              0.015 * Real.sqrt (D * S * A * T) ≤
                ∫ h, mdpRegret M T h ∂(mdpMeasure M (mdpStateDirac s) π T) := by
  sorry
