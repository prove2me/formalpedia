-- Prove2me | Theorems.Thm_BanditAlgorithm_jao_collapsed_two_state_bandit_core
-- name    : BanditAlgorithm.jao_collapsed_two_state_bandit_core
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-05T17:03:06.575734+00:00
-- url     : https://prove2.me/theorems/098d5d5f-5251-4742-ba6c-d592d7f9ae96
-- title:
--   JAO Section 6, eqs. (34)-(37) and Lemma 13: the collapsed two-state MDP forces regret $\Omega(\sqrt{D' m T})$
-- statement:
--   There is a universal constant $c > 0$ such that for every $m \ge 20$, every $\delta \in (0, \tfrac13]$ and every horizon $T$ with $16m \le \delta T$, and for **every** learning algorithm $\pi$ on the two-state, $m$-action MDP, one can plant a good action $a$ and an advantage $\varepsilon \in (0, \delta]$ so that the resulting MDP $M$ forces expected regret at least $c\sqrt{Tm/\delta}$ from the initial state $s_\circ$.
--
--   Here `M` is the two-state gadget of JAO Figure 3, presented by its defining equations rather than through an auxiliary definition: state $0$ is $s_\circ$ with reward $0$, state $1$ is $s_p$ with reward $1$, the return probability is $p(s_\circ \mid s_p, b) = \delta$ for every action $b$, and the escape probability is $p(s_p \mid s_\circ, b) = \delta$ for every action except the single planted action $a$, for which it is $\delta + \varepsilon$. The gadget has diameter $D' = 1/\delta$, so the conclusion $c\sqrt{Tm/\delta} = c\sqrt{D'mT}$ is the $\Omega(\sqrt{D'kA'T})$ of the paper with $m = kA'$.
--
--   This is the probabilistic core of the lower bound of Jaksch, Ortner and Auer (2010), Section 6. After the composite MDP is collapsed by identifying all $s_\circ$-states, the problem becomes an ordinary multi-armed bandit with $m = kA'$ arms, and the argument is that of Auer et al. (2002b), Theorem A.2. Writing $N_p$, $N_\circ$ and $N_\circ^*$ for the number of visits to $s_p$, the number of visits to $s_\circ$, and the number of plays of the planted action in $s_\circ$, equations (34) and (35) give
--   $$\mathbb{E}_a\!\left[R(M, \pi, s_\circ, T)\right] \;\le\; \frac{T}{2} + \mathbb{E}_a[N_\circ^*]\,\varepsilon D' + \frac{D'}{2},$$
--   Lemma 13 — a Pinsker-type bound stating that for $f : \{s_\circ, s_p\}^{T+1} \to [0,B]$ one has $\mathbb{E}_a[f] \le \mathbb{E}_{\mathrm{unif}}[f] + \tfrac{B}{2}\tfrac{\varepsilon}{\sqrt{\delta}}\sqrt{2\mathbb{E}_{\mathrm{unif}}[N_\circ^*]}$ — controls $\mathbb{E}_a[N_\circ^*]$ in (37), and Jensen's inequality across the $m$ possible plantings yields the average bound. Choosing $\varepsilon := \tfrac15\sqrt{mD'/T}$, which satisfies $\varepsilon \le \delta$ precisely because $16m \le \delta T$, makes the average regret exceed a constant multiple of $\sqrt{D'mT}$, and a planting achieving at least the average exists by the probabilistic method.
--
--   The hypotheses are exactly those the argument needs: $\delta \le \tfrac13$ is JAO's standing assumption (used to get $\varepsilon \le \delta \le 1 - 2\delta$, the range required by Lemma 13), $m \ge 20$ is their $kA' \ge 20$, and $16m \le \delta T$ is their $D' \le T/(16kA')$, which is what the hypothesis $T \ge DSA$ of Theorem 5 supplies.
--
--   Note that the observation sequence in an MDP consists of the next state as well as the reward, not the reward alone; JAO point out that this is harmless here because the reward is a deterministic function of the state, so $N_\circ^*$ remains a function of the state sequence and Lemma 13 applies unchanged.
-- source:
--   Jaksch, Ortner & Auer, "Near-optimal Regret Bounds for Reinforcement Learning", JMLR 11 (2010) 1563-1600, Section 6 (pp. 1582-1586): the construction of Figures 3-4 and the analysis in equations (34)-(37) together with Lemma 13; Lemma 13 is adapted from Auer, Cesa-Bianchi, Freund & Schapire, "The Nonstochastic Multiarmed Bandit Problem", SIAM J. Comput. 32 (2002) 48-77, Theorem A.2.

import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_FiniteMDPLearning

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.jao_collapsed_two_state_bandit_core :
    ∃ c : ℝ, 0 < c ∧
      ∀ m : ℕ, 20 ≤ m → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 3 →
        ∀ T : ℕ, (16 : ℝ) * m ≤ δ * T →
          ∀ π : MDPPolicy 2 m,
            ∃ (a : Fin m) (ε : ℝ) (M : FiniteMDP 2 m),
              0 < ε ∧ ε ≤ δ ∧
              (∀ b, M.r 0 b = 0) ∧ (∀ b, M.r 1 b = 1) ∧
              (∀ b, (M.P 1 b 0 : ℝ) = δ) ∧
              (∀ b, (M.P 0 b 1 : ℝ) = δ + (if b = a then ε else 0)) ∧
              c * Real.sqrt ((T : ℝ) * m / δ) ≤
                ∫ h, mdpRegret M T h ∂(mdpMeasure M (mdpStateDirac 0) π T) := by
  sorry
