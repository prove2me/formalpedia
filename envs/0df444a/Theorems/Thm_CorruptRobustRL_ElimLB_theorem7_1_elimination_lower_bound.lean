-- Prove2me | Theorems.Thm_CorruptRobustRL_ElimLB_theorem7_1_elimination_lower_bound
-- name    : CorruptRobustRL.ElimLB.theorem7_1_elimination_lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-13T20:52:05.596869+00:00
-- url     : https://prove2.me/theorems/2d946995-2064-447f-abd9-959e586a28bc
-- title:
--   Theorem 7.1, p. 32 — uniformly action-eliminating, uniformly admissible algorithms suffer expected regret ≥ K/8 for K ≤ A^H/4
-- statement:
--   For every horizon $H\ge1$ and every $A\ge2$, consider the MDP environment $\mathscr E=(\mathcal X,\mathcal A,H)$ with $|\mathcal X|=H+1$ states and $|\mathcal A|=A$ actions. There is a stochastic problem instance $\mathcal M$ on $\mathscr E$ with the following property. Let an algorithm be **uniformly action-eliminating**: before each episode $k$ it produces a Q-supervisor $\mathcal T_k=(\bar Q_k,\underline Q_k,\mathscr A_k,\pi^{\mathrm{ucb}}_k)$, and at each stage it plays an action drawn independently and uniformly from the plausible set $\mathscr A^{\mathrm{plaus}}_{k;h}(x)$. Let it also be **uniformly admissible** for $\mathscr E$ over $K$ episodes: for every problem instance on $\mathscr E$, with probability at least $\tfrac12$ all of $\mathcal T_1,\dots,\mathcal T_K$ are confidence-admissible for that instance. If
--
--   $$
--   K\le\frac{A^H}{4},\qquad\text{then}\qquad \mathbb E^{\mathcal M}\bigl[\mathrm{Regret}^{\mathcal M}_K\bigr]\ \ge\ \frac K8 .
--   $$
--
--   Uniform elimination from plausible sets, which suffices for corruption-robust multi-armed bandits, therefore suffers linear regret for exponentially many episodes in episodic reinforcement learning, even when its confidence sets are correct.
--
--   **Formalization Note** States are `Fin (H+1)`, actions `Fin A` (the redundant instance `NeZero A` makes `Fin A` nonempty), stages and episodes are 0-based. Three choices are pinned. (1) Uniform admissibility is the joint event $\mathbb P[\bigcap_{k\le K}\mathcal E^{\mathrm{adm}}_k]\ge\tfrac12$ for every instance, the hypothesis the proof states on p. 39 ("By assumption, we have…"); §7 words it per supervisor. (2) The algorithm is a kernel from the observed history (past supervisors and observed episodes) to a discrete law of the next supervisor, and an empty plausible set is replaced by $\mathcal A$. (3) Instances in the hypothesis have discrete reward laws on $[0,1]$, which weakens the hypothesis. The existential instance is the paper's $\mathcal M$; it is not fixed in the statement.
-- source:
--   Lykouris, Simchowitz, Slivkins & Sun, Corruption-robust exploration in episodic reinforcement learning, arXiv:1911.08689v4, p. 32, Theorem 7.1 (definitions p. 31, §7; proof pp. 38–39, App. A)

import Mathlib
import Definitions.Def_CorruptRobustRL_ElimLB_MDP
import Definitions.Def_CorruptRobustRL_ElimLB_Setting
import Definitions.Def_CorruptRobustRL_ElimLB_ComboLock

namespace CorruptRobustRL.ElimLB

/-- Theorem 7.1, arXiv:1911.08689v4, p. 32: for every `H ≥ 1` and `A ≥ 2` there is a stochastic
instance `ℳ` on the environment with `H + 1` states and `A` actions such that every uniformly
action-eliminating algorithm that is uniformly admissible for the environment has expected regret
at least `K/8` over `K ≤ A^H/4` episodes. -/
theorem theorem7_1_elimination_lower_bound (H A : ℕ) [NeZero A] (hH : 1 ≤ H) (hA : 2 ≤ A) :
    ∃ M : Instance (Fin (H + 1)) (Fin A),
      ∀ (L : Learner (Fin (H + 1)) (Fin A) H) (K : ℕ),
        UniformlyAdmissible L K → (K : ℝ) ≤ (A : ℝ) ^ H / 4 →
          (K : ℝ) / 8 ≤ expRegret M L K := by sorry

end CorruptRobustRL.ElimLB
