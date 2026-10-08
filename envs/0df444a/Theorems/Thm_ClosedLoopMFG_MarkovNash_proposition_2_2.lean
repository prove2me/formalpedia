-- Prove2me | Theorems.Thm_ClosedLoopMFG_MarkovNash_proposition_2_2
-- name    : ClosedLoopMFG.MarkovNash.proposition_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:32:11.637879+00:00
-- url     : https://prove2.me/theorems/637cc2d5-4d3d-4699-86d2-359b81b218c4
-- title:
--   Proposition 2.2 — under Assumptions A and B every Markovian $\epsilon$-Nash equilibrium is a closed-loop $\epsilon$-Nash equilibrium
-- statement:
--   Suppose Assumptions A and B hold, and let $\epsilon\ge0$. Let $n\ge1$ and let $(\alpha^1,\dots,\alpha^n)\in\mathcal{AM}_n^n$ be a Markovian $\epsilon$-Nash equilibrium of the $n$-player game, i.e. for every $i$,
--   $$J^n_i(\alpha^1,\dots,\alpha^n)\ge\sup_{\beta\in\mathcal{AM}_n}J^n_i(\alpha^1,\dots,\alpha^{i-1},\beta,\alpha^{i+1},\dots,\alpha^n)-\epsilon.$$
--   Then $(\alpha^1,\dots,\alpha^n)$, viewed as closed-loop controls $\alpha^i(t,\boldsymbol x)=\alpha^i(t,\boldsymbol x_t)$, is a closed-loop $\epsilon$-Nash equilibrium: for every $i$,
--   $$J^n_i(\alpha^1,\dots,\alpha^n)\ge\sup_{\beta\in\mathcal A_n}J^n_i(\alpha^1,\dots,\alpha^{i-1},\beta,\alpha^{i+1},\dots,\alpha^n)-\epsilon.$$
--
--   The Markovian notion compares only against Markovian deviations, so a priori the two equilibrium notions are unrelated; under the convexity Assumption B the Markovian equilibria form a subset of the closed-loop equilibria. This lets the paper's limit theorems for closed-loop equilibria apply to Markovian ones.
--
--   **Formalization Note** $n\ge1$ is a type-class hypothesis and $T>0$ is explicit. Payoffs are computed on weak solutions, and both $\epsilon$-Nash notions are required for every solution of the profiles involved (see the `Game` definition); this agrees with the paper because solutions exist and are unique in law (Section 2.1, p. 6). The hypothesis compares against Markovian deviations only; the conclusion compares against every admissible closed-loop deviation.
-- source:
--   Lacker, On the convergence of closed-loop Nash equilibria to the mean field game limit, arXiv:1808.02745v1, p. 7, Proposition 2.2 (proof in Section 4.3, pp. 20–21)

import Mathlib
import Definitions.Def_ClosedLoopMFG_MarkovNash_Model
import Definitions.Def_ClosedLoopMFG_MarkovNash_Game

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ClosedLoopMFG.MarkovNash

/-- Lacker, arXiv:1808.02745v1, Proposition 2.2 (p. 7): under Assumptions A and B, for `ε ≥ 0`,
every Markovian `ε`-Nash equilibrium of the `n`-player game (`n ≥ 1`) is also a closed-loop
`ε`-Nash equilibrium: no player can gain more than `ε` by deviating to any closed-loop
(path-dependent) control. -/
theorem proposition_2_2 {n d : ℕ} [NeZero n] {T : ℝ≥0} (hT : 0 < T)
    {EA : Type*} [NormedAddCommGroup EA] [NormedSpace ℝ EA] [MeasurableSpace EA] [BorelSpace EA]
    (A : Set EA) (lam : PR d) (b : ℝ → E d → PR d → EA → E d)
    (f : ℝ → E d → PR d → EA → ℝ) (g : E d → PR d → ℝ)
    (hA : AssumptionA T A b f g) (hB : AssumptionB T A b f)
    (ε : ℝ) (hε : 0 ≤ ε) (α : Fin n → ℝ → (Fin n → E d) → EA)
    (hα : IsMarkovianNash T A lam b f g ε α) :
    IsClosedLoopNash A lam b f g ε (fun i => liftM (T := T) (α i)) := by sorry

end ClosedLoopMFG.MarkovNash
