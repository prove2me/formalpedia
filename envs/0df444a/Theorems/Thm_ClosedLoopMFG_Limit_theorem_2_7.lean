-- Prove2me | Theorems.Thm_ClosedLoopMFG_Limit_theorem_2_7
-- name    : ClosedLoopMFG.Limit.theorem_2_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:31:52.201374+00:00
-- url     : https://prove2.me/theorems/d2624fcb-6b87-4e50-95d3-7a172644205e
-- title:
--   Theorem 2.7 — empirical measure flows of closed-loop $\varepsilon_n$-Nash equilibria are tight, and every limit is a weak MFE
-- statement:
--   Assume Assumptions A and B. Let $\varepsilon_n\ge0$ with $\varepsilon_n\to0$, and for each $n$ let $\alpha^n=(\alpha^{n,1},\dots,\alpha^{n,n})$ be a closed-loop $\varepsilon_n$-Nash equilibrium of the $n$-player game, with state processes
--   $$dX^{n,i}_t=b\big(t,X^{n,i}_t,\mu^n_t,\alpha^{n,i}(t,X^n)\big)\,dt+dW^i_t,\qquad\mu^n_t=\frac1n\sum_{k=1}^n\delta_{X^{n,k}_t}.$$
--   Then:
--
--   1. the empirical measure flows $\mu^n=\mu^n[\alpha^n]$ form a tight family of $C([0,T];\mathcal P(\mathbb R^d))$-valued random variables, i.e. their laws form a tight subset of $\mathcal P(C([0,T];\mathcal P(\mathbb R^d)))$;
--   2. every limit in distribution is a weak MFE: whenever, along a subsequence $n_k$, the laws of $\mu^{n_k}$ converge weakly to some $\nu$, there is a weak semi-Markov mean field equilibrium (on some complete filtered probability space) whose measure flow $\mu$ has law $\nu$.
--
--   This is the main result of the paper: under the Filippov–Roxin convexity condition, every limit of closed-loop (path-dependent) $n$-player Nash equilibria is a weak semi-Markov MFE, in which the equilibrium control depends on the current state and the past of the (possibly random) measure flow.
--
--   **Formalization Note** Term $n$ of the sequence is the game with $n+1$ players, and $\varepsilon_n$ carries the same index; an index shift changes neither tightness nor the limits. The flows are those of arbitrary weak solutions of the equilibrium state systems, which by uniqueness in law (Section 2.1) have the paper's law $\mathcal L(\mu^n[\alpha^n])$. "Every limit in distribution" quantifies over all subsequential limits, which includes the limit of the whole sequence. The conclusion is the existence of a weak MFE on some probability space with the given flow law, not on the $n$-player spaces. Weak MFE is the predicate of the `Equilibrium` file (optimality against the solutions of (2.2) adapted to the completed filtration of $(X^*_0,W,\mu)$, as in Remark 2.6).
-- source:
--   Lacker, On the convergence of closed-loop Nash equilibria to the mean field game limit, arXiv:1808.02745v1, p. 8, Theorem 2.7

import Mathlib
import Definitions.Def_ClosedLoopMFG_Limit_Model
import Definitions.Def_ClosedLoopMFG_Limit_Game
import Definitions.Def_ClosedLoopMFG_Limit_Equilibrium

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace ClosedLoopMFG.Limit

/-- **Theorem 2.7** (Lacker, arXiv:1808.02745v1, p. 8). Under Assumptions A and B, let
`ε_n ≥ 0`, `ε_n → 0`, and let `αⁿ` be a closed-loop `ε_n`-Nash equilibrium of the game with
`n + 1` players. Then the laws of the empirical measure flows `μⁿ = μⁿ[αⁿ]` are tight in
`P(C([0, T]; P(ℝ^d)))`, and every limit in distribution of a subsequence is the law of the flow
of a weak MFE. -/
theorem theorem_2_7 {d : ℕ} {T : ℝ≥0} (hT : 0 < T) {EA : Type} [NormedAddCommGroup EA]
    [NormedSpace ℝ EA] [MeasurableSpace EA] [BorelSpace EA] (A : Set EA) (lam : PR d)
    (b : ℝ → E d → PR d → EA → E d) (f : ℝ → E d → PR d → EA → ℝ) (g : E d → PR d → ℝ)
    (hA : AssumptionA T A b f g) (hB : AssumptionB T A b f)
    (ε : ℕ → ℝ) (hε0 : ∀ n, 0 ≤ ε n) (hε : Tendsto ε atTop (𝓝 0))
    (α : (n : ℕ) → Fin (n + 1) → ℝ → (Fin (n + 1) → Path d T) → EA)
    (hα : ∀ n, IsClosedLoopNash A lam b f g (ε n) (α n))
    (S : (n : ℕ) → NSol (n + 1) d T lam (drift b (α n))) :
    IsTightMeasureSet (Set.range fun n => ((S n).law : Measure (Flow d T))) ∧
    ∀ φ : ℕ → ℕ, StrictMono φ → ∀ ν : ProbabilityMeasure (Flow d T),
      Tendsto (fun k => (S (φ k)).law) atTop (𝓝 ν) → IsWeakMFELaw A lam b f g ν := by sorry

end ClosedLoopMFG.Limit
