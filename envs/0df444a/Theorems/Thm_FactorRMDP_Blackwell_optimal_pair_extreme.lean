-- Prove2me | Theorems.Thm_FactorRMDP_Blackwell_optimal_pair_extreme
-- name    : FactorRMDP.Blackwell.optimal_pair_extreme
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:26:19.553368+00:00
-- url     : https://prove2.me/theorems/122180b9-dbf9-477a-9c57-6629afedad38
-- title:
--   Appendix G.1, p. 26 — for each λ some optimal pair has π_λ deterministic and W_λ an extreme point of 𝒲
-- statement:
--   Let $\mathcal W$ be an $r$-rectangular uncertainty set of factor matrices and let $\lambda\in(0,1)$. Then the robust MDP problem (1.2) with discount $\lambda$ has an optimal solution $(\pi_\lambda,W_\lambda)$ in which $\pi_\lambda$ is stationary and deterministic and $W_\lambda$ is an extreme point of $\mathcal W$:
--   $$
--   \exists\,(\pi_\lambda,W_\lambda):\quad \pi_\lambda\ \text{deterministic},\quad (\pi_\lambda,W_\lambda)\ \text{optimal for (1.2) at }\lambda,\quad W_\lambda\in\operatorname{ext}\mathcal W .
--   $$
--
--   When every factor set has finitely many extreme points, this places an optimal pair, for every discount, inside one finite set of candidate pairs, which is the starting point of the proof of robust Blackwell optimality.
--
--   **Formalization Note** The proof of Proposition 6.2 says of a given solution with $\pi_\lambda$ deterministic that "from (5.1), the factor matrix $W_\lambda$ belongs to the set of extreme points of $\mathcal W$". Read for every such solution this is false (an optimal factor matrix can be a non-extreme point when the reward does not depend on some factor); the proof only needs one such pair, and that existence statement is what is posed. Extreme points are those of $\mathcal W$ itself (Mathlib's `Set.extremePoints`), not of the factor sets.
-- source:
--   Goyal and Grand-Clément, Robust Markov Decision Process: Beyond Rectangularity, arXiv:1811.00215v8 (2021), p. 26, Appendix G.1, proof of Proposition 6.2 ("From (5.1), the factor matrix W_λ belongs to the set of extreme points of 𝒲")

import Mathlib
import Definitions.Def_FactorRMDP_Blackwell_Model

namespace FactorRMDP.Blackwell

/-- Appendix G.1, proof of Proposition 6.2 (p. 26): for every discount λ ∈ (0, 1) there is a
solution (π_λ, W_λ) of the robust MDP problem (1.2) with π_λ stationary deterministic and W_λ an
extreme point of 𝒲. The paper says "from (5.1), the factor matrix W_λ belongs to the set of
extreme points of 𝒲" of a given solution; read for every solution this is false (an optimal W
need not be extreme), and the proof uses only the existence of one such pair, which we state. -/
theorem optimal_pair_extreme {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S]
    [DecidableEq A] [Nonempty A] {r : ℕ} (M : Model S A r) (hR : M.IsRRect)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    ∃ πs : S → A → ℝ, ∃ Ws : Fin r → S → ℝ,
      FactorRMDP.ValueIter.IsDeterministic πs ∧ M.IsRobustSolution lam πs Ws ∧ Ws ∈ Set.extremePoints ℝ M.Wset := by sorry

end FactorRMDP.Blackwell
