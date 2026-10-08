-- Prove2me | Theorems.Thm_ClosedLoopMFG_Converse_theorem_2_11
-- name    : ClosedLoopMFG.Converse.theorem_2_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T04:29:42.700232+00:00
-- url     : https://prove2.me/theorems/8594c5b9-1bcb-4077-859a-aa72764cbfa3
-- title:
--   Theorem 2.11 — every strong MFE is the limit in law of Markovian $\epsilon_n$-Nash equilibria
-- statement:
--   Suppose Assumptions A, B and C hold, and let $m\in C([0,T];\mathcal P(\mathbb R^d))$ be a strong mean field equilibrium. Then there exist the following:
--   - numbers $\epsilon_n\ge0$ with $\epsilon_n\to0$;
--   - for each $n$, a Markovian $\epsilon_n$-Nash equilibrium $\alpha^n=(\alpha^{n,1},\dots,\alpha^{n,n})$ of the $n$-player game, whose state system has a solution;
--
--   such that the empirical measure flows satisfy
--   $$\mu^n[\alpha^n]\ \longrightarrow\ m\quad\text{in law in } C([0,T];\mathcal P(\mathbb R^d)).$$
--
--   This is the partial converse of the paper's main limit theorem: every classical (strong) mean field equilibrium arises as the limit of $n$-player approximate Nash equilibria in Markovian feedback form, with a drift that is only total-variation Lipschitz in the measure and with possibly discontinuous equilibrium feedback.
--
--   **Formalization Note**
--   - Nash equilibria quantify over solutions of the state systems, so the conclusion also asserts that each equilibrium's state system has a solution; otherwise an equilibrium could hold vacuously.
--   - "$\mu^n[\alpha^n]$ converges in law to $m$" is convergence of the laws of $\mu^n$ to the Dirac mass $\delta_m$, asserted for every choice of solutions (unique in law).
--   - The game with $n+1$ players is indexed by $n\in\mathbb N$; a shift of index changes no limit.
--   - $T>0$ is the paper's standing assumption.
-- source:
--   Lacker, On the convergence of closed-loop Nash equilibria to the mean field game limit, arXiv:1808.02745v1, p. 10, Theorem 2.11

import Mathlib
import Definitions.Def_ClosedLoopMFG_Converse_Model
import Definitions.Def_ClosedLoopMFG_Converse_Game
import Definitions.Def_ClosedLoopMFG_Converse_Equilibrium

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace ClosedLoopMFG.Converse

theorem theorem_2_11 {d : ℕ} {T : ℝ≥0} (hT : 0 < T) {EA : Type}
    [NormedAddCommGroup EA] [NormedSpace ℝ EA] [MeasurableSpace EA] [BorelSpace EA]
    (A : Set EA) (lam : PR d) (b : ℝ → ClosedLoopMFG.Limit.E d → PR d → EA → ClosedLoopMFG.Limit.E d) (f : ℝ → ClosedLoopMFG.Limit.E d → PR d → EA → ℝ)
    (g : ClosedLoopMFG.Limit.E d → PR d → ℝ)
    (hA : AssumptionA T A b f g) (hB : AssumptionB T A b f) (hC : AssumptionC T A b)
    (m : Flow d T) (hm : IsStrongMFE T A lam b f g m) :
    ∃ ε : ℕ → ℝ, (∀ n, 0 ≤ ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
      ∃ α : (n : ℕ) → Fin (n + 1) → ℝ → (Fin (n + 1) → ClosedLoopMFG.Limit.E d) → EA,
        (∀ n, IsMarkovNash T A lam b f g (ε n) (α n)) ∧
        (∀ n, Nonempty (NSol (n + 1) d T lam (driftM T b (α n)))) ∧
        ∀ S : (n : ℕ) → NSol (n + 1) d T lam (driftM T b (α n)),
          Tendsto (fun n => (S n).law) atTop (𝓝 (diracFlow m)) := by sorry

end ClosedLoopMFG.Converse
