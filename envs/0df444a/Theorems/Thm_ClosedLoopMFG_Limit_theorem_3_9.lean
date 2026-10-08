-- Prove2me | Theorems.Thm_ClosedLoopMFG_Limit_theorem_3_9
-- name    : ClosedLoopMFG.Limit.theorem_3_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:32:03.488337+00:00
-- url     : https://prove2.me/theorems/b4016d55-c611-4ed7-9783-ed986bef73dc
-- title:
--   Theorem 3.9 — without convexity, limits of closed-loop $\varepsilon_n$-Nash equilibria are weak RMFE
-- statement:
--   Assume Assumption A. Let $\varepsilon_n\ge0$ with $\varepsilon_n\to0$, and for each $n$ let $\alpha^n=(\alpha^{n,1},\dots,\alpha^{n,n})$ be a closed-loop $\varepsilon_n$-Nash equilibrium of the $n$-player game. Then the empirical measure flows $\mu^n=\mu^n[\alpha^n]$ are tight as $C([0,T];\mathcal P(\mathbb R^d))$-valued random variables, and every limit in distribution is a weak RMFE: for every subsequence along which the laws of $\mu^n$ converge to some $\nu$, there is a weak RMFE whose measure flow has law $\nu$.
--
--   The convexity Assumption B is not needed; Theorem 2.7 follows from this theorem and Proposition 3.7.
--
--   **Formalization Note** Term $n$ of the sequence is the game with $n+1$ players, and $\varepsilon_n$ carries the same index. "Every limit in distribution" quantifies over all subsequential limits $\nu$ of the laws. The weak RMFE may live on any probability space; only the law of its flow is identified with $\nu$. The flows are those of arbitrary weak solutions of the equilibrium state systems (their laws do not depend on the choice).
-- source:
--   Lacker, On the convergence of closed-loop Nash equilibria to the mean field game limit, arXiv:1808.02745v1, p. 18, Theorem 3.9

import Mathlib
import Definitions.Def_ClosedLoopMFG_Limit_Model
import Definitions.Def_ClosedLoopMFG_Limit_Game
import Definitions.Def_ClosedLoopMFG_Limit_Equilibrium

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace ClosedLoopMFG.Limit

/-- **Theorem 3.9** (p. 18). Under Assumption A alone, the empirical measure flows of closed-loop
`ε_n`-Nash equilibria (`ε_n ≥ 0`, `ε_n → 0`) have tight laws, and every subsequential limit in
distribution is the law of the flow of a weak RMFE. -/
theorem theorem_3_9 {d : ℕ} {T : ℝ≥0} (hT : 0 < T) {EA : Type} [NormedAddCommGroup EA]
    [NormedSpace ℝ EA] [MeasurableSpace EA] [BorelSpace EA] (A : Set EA) (lam : PR d)
    (b : ℝ → E d → PR d → EA → E d) (f : ℝ → E d → PR d → EA → ℝ) (g : E d → PR d → ℝ)
    (hA : AssumptionA T A b f g)
    (ε : ℕ → ℝ) (hε0 : ∀ n, 0 ≤ ε n) (hε : Tendsto ε atTop (𝓝 0))
    (α : (n : ℕ) → Fin (n + 1) → ℝ → (Fin (n + 1) → Path d T) → EA)
    (hα : ∀ n, IsClosedLoopNash A lam b f g (ε n) (α n))
    (S : (n : ℕ) → NSol (n + 1) d T lam (drift b (α n))) :
    IsTightMeasureSet (Set.range fun n => ((S n).law : Measure (Flow d T))) ∧
    ∀ φ : ℕ → ℕ, StrictMono φ → ∀ ν : ProbabilityMeasure (Flow d T),
      Tendsto (fun k => (S (φ k)).law) atTop (𝓝 ν) → IsWeakRMFELaw A lam b f g ν := by sorry

end ClosedLoopMFG.Limit
