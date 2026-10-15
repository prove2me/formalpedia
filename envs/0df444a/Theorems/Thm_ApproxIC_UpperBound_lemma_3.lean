-- Prove2me | Theorems.Thm_ApproxIC_UpperBound_lemma_3
-- name    : ApproxIC.UpperBound.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:42:21.717067+00:00
-- url     : https://prove2.me/theorems/d050e8bc-9961-4512-9db2-06fd3d4731a1
-- title:
--   Lemma 3, p. 20 — Φ₁(λ^IC) ≤ C·ε·K with an absolute constant C
-- statement:
--   There is an absolute constant $C>0$ such that for every value density satisfying the standing assumptions, every path $(\mu,\nu_0,v^\star,w)$ with number of steps $K$, and every $\varepsilon\ge 0$, Lemma 2's dual solution $\lambda^\star$ satisfies
--   $$\Phi_1(\lambda^\star)=\varepsilon\int_\mu^{\bar v}\lambda^\star(v)\,dv\le C\cdot\varepsilon\cdot K .$$
--
--   This bounds the cost of the $\varepsilon$-relaxation by the number of steps the path needs to reach $\mu$; with Proposition 2 it yields $\Phi_1=\tilde O(\varepsilon^{1-\beta})$.
--
--   **Formalization Note** The page leaves the dependence of $C$ unstated; the proof (pp. 39–40) shows $\int_\mu^{\bar v}\lambda^\star\le K+1\le 2K$ (as $K\ge 1$), so $C$ is stated before the density and the path, as an absolute constant. $\lambda^\star$ is Lemma 2's explicit function, not an arbitrary feasible dual variable. $K$ is `steps P`.
-- source:
--   Balseiro, Besbes, Castro, Mechanism Design under Approximate Incentive Compatibility, arXiv:2103.03403v2 (2022), p. 20, Lemma 3 (proof pp. 39–40)

import Mathlib
import Definitions.Def_ApproxIC_UpperBound_Path

namespace ApproxIC.UpperBound

theorem lemma_3 :
    ∃ C > 0, ∀ (M : Model), M.Standing → ∀ (P : Path M) (ε : ℝ), 0 ≤ ε →
      Phi1 M P ε (lamStar M P) ≤ C * ε * (steps P : ℝ) := by sorry

end ApproxIC.UpperBound
