-- Prove2me | Theorems.Thm_ClosedLoopMFG_Converse_theorem_3_10
-- name    : ClosedLoopMFG.Converse.theorem_3_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T04:29:07.103032+00:00
-- url     : https://prove2.me/theorems/657ea51e-3b1e-4d73-abdf-3f2fe525506c
-- title:
--   Theorem 3.10 — every strong RMFE is the limit of relaxed Markovian $\epsilon_n$-Nash equilibria
-- statement:
--   Suppose Assumptions A and C hold, and let $m\in C([0,T];\mathcal P(\mathbb R^d))$ be a strong RMFE. Then there exist the following:
--   - numbers $\epsilon_n\ge0$ with $\epsilon_n\to0$;
--   - for each $n$, a relaxed Markovian $\epsilon_n$-Nash equilibrium $\Lambda^n$ of the $n$-player game, whose state system has a solution;
--
--   such that
--   $$\mu^n[\Lambda^n]\ \longrightarrow\ m\quad\text{in law in } C([0,T];\mathcal P(\mathbb R^d)).$$
--
--   This is the relaxed version of the converse limit theorem. It needs no convexity (Assumption B), and Theorem 2.11 follows from it and Propositions 3.4(a) and 3.7.
--
--   **Formalization Note** With Nash equilibria defined by quantifying over solutions, a profile without solutions would be an equilibrium vacuously, so the conclusion also asserts that each $\Lambda^n$ has a solution. The convergence in law is asserted for every choice of solutions (they are unique in law), as convergence of the laws of $\mu^n$ to $\delta_m$. The game with $n+1$ players is indexed by $n$.
-- source:
--   Lacker, On the convergence of closed-loop Nash equilibria to the mean field game limit, arXiv:1808.02745v1, p. 18, Theorem 3.10

import Mathlib
import Definitions.Def_ClosedLoopMFG_Converse_Model
import Definitions.Def_ClosedLoopMFG_Converse_Game
import Definitions.Def_ClosedLoopMFG_Converse_Equilibrium

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace ClosedLoopMFG.Converse

theorem theorem_3_10 {d : ℕ} {T : ℝ≥0} (hT : 0 < T) {EA : Type}
    [NormedAddCommGroup EA] [NormedSpace ℝ EA] [MeasurableSpace EA] [BorelSpace EA]
    (A : Set EA) (lam : PR d) (b : ℝ → ClosedLoopMFG.Limit.E d → PR d → EA → ClosedLoopMFG.Limit.E d) (f : ℝ → ClosedLoopMFG.Limit.E d → PR d → EA → ℝ)
    (g : ClosedLoopMFG.Limit.E d → PR d → ℝ)
    (hA : AssumptionA T A b f g) (hC : AssumptionC T A b)
    (m : Flow d T) (hm : IsStrongRMFE T A lam b f g m) :
    ∃ ε : ℕ → ℝ, (∀ n, 0 ≤ ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
      ∃ Λ : (n : ℕ) → Fin (n + 1) → ℝ → (Fin (n + 1) → ClosedLoopMFG.Limit.E d) → PA A,
        (∀ n, IsRelaxedMarkovNash T A lam b f g (ε n) (Λ n)) ∧
        (∀ n, Nonempty (NSol (n + 1) d T lam (driftR T b (Λ n)))) ∧
        ∀ S : (n : ℕ) → NSol (n + 1) d T lam (driftR T b (Λ n)),
          Tendsto (fun n => (S n).law) atTop (𝓝 (diracFlow m)) := by sorry

end ClosedLoopMFG.Converse
