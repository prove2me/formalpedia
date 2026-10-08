-- Prove2me | Theorems.Thm_ClosedLoopMFG_Limit_lemma_5_1
-- name    : ClosedLoopMFG.Limit.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:31:55.162661+00:00
-- url     : https://prove2.me/theorems/f74a72d7-adff-43e1-861d-1efbb151f4c3
-- title:
--   Lemma 5.1 — the path-space empirical measures are tight
-- statement:
--   Assume Assumption A. Let $(\alpha^n)$ be an arbitrary sequence of profiles of admissible closed-loop controls, $\alpha^n=(\alpha^{n,1},\dots,\alpha^{n,n})$, and let $X^n=(X^{n,1},\dots,X^{n,n})$ be the corresponding state processes (5.1). Define the **path-space empirical measure**
--   $$\boldsymbol\mu^n=\frac1n\sum_{k=1}^n\delta_{X^{n,k}},$$
--   a random element of $\mathcal P(\mathcal C^d)$. Then $(\boldsymbol\mu^n)$ is a tight family of $\mathcal P(\mathcal C^d)$-valued random variables: the laws of $\boldsymbol\mu^n$ form a tight subset of $\mathcal P(\mathcal P(\mathcal C^d))$.
--
--   This is the compactness step of the proof of the main limit theorem; the Nash property is not used.
--
--   **Formalization Note** The statement concerns measures on paths, not measure flows. Term $n$ of the sequence is the game with $n+1$ players. The conclusion also asserts that each $\boldsymbol\mu^n$ is a measurable map into $\mathcal P(\mathcal C^d)$ (with the Borel $\sigma$-field of the weak topology), which the paper's phrase "random variables" presupposes and which keeps the push-forward laws from being degenerate.
-- source:
--   Lacker, On the convergence of closed-loop Nash equilibria to the mean field game limit, arXiv:1808.02745v1, p. 24, Lemma 5.1

import Mathlib
import Definitions.Def_ClosedLoopMFG_Limit_Model
import Definitions.Def_ClosedLoopMFG_Limit_Game

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace ClosedLoopMFG.Limit

/-- **Lemma 5.1** (p. 24). For an arbitrary sequence of admissible profiles `αⁿ` (term `n` is the
game with `n + 1` players) and weak solutions of (5.1), the path-space empirical measures
`μⁿ = (1/n) ∑_k δ_{X^{n,k}}` are `P(𝒞^d)`-valued random variables whose laws form a tight family. -/
theorem lemma_5_1 {d : ℕ} {T : ℝ≥0} (hT : 0 < T) {EA : Type} [NormedAddCommGroup EA]
    [NormedSpace ℝ EA] [MeasurableSpace EA] [BorelSpace EA] (A : Set EA) (lam : PR d)
    (b : ℝ → E d → PR d → EA → E d) (f : ℝ → E d → PR d → EA → ℝ) (g : E d → PR d → ℝ)
    (hA : AssumptionA T A b f g)
    (α : (n : ℕ) → Fin (n + 1) → ℝ → (Fin (n + 1) → Path d T) → EA)
    (hα : ∀ n i, IsAdmissible A (α n i))
    (S : (n : ℕ) → NSol (n + 1) d T lam (drift b (α n))) :
    (∀ n, Measurable fun ω => empiricalMeasure ((S n).X ω)) ∧
    IsTightMeasureSet
      (Set.range fun n => (S n).P.map (fun ω => empiricalMeasure ((S n).X ω))) := by sorry

end ClosedLoopMFG.Limit
