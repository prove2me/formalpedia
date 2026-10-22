-- Prove2me | Theorems.Thm_BoundedEntropyGames_ConvRate_eq_18_19
-- name    : BoundedEntropyGames.ConvRate.eq_18_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:15:30.115637+00:00
-- url     : https://prove2.me/theorems/ec5aa59c-b394-4e95-8479-68a2db3f466a
-- title:
--   (18)–(19), p. 20 — two-point representation of $J^{(A)}_{cav}(H(X|Y))$
-- statement:
--   Consider a stage game with finite nonempty action sets $\mathcal A,\mathcal B$ and payoffs $u_{ab}$, and a joint pmf $p_{XY}$. There exist $r\in[0,1]$ and pmfs $p^{(1)}_A,p^{(2)}_A\in\Delta(\mathcal A)$ such that
--   $$
--   rU^{(A)}(p^{(1)}_A)+(1-r)U^{(A)}(p^{(2)}_A)=J^{(A)}_{cav}(H(X|Y)),\qquad rH(p^{(1)}_A)+(1-r)H(p^{(2)}_A)\le H(X|Y).
--   $$
--
--   The mixture fixes the constant $r$ of Theorem 6 and the two target laws that Alice's block strategy simulates.
--
--   **Formalization Note** $J^{(A)}_{cav}$ is the least concave majorant of $J^{(A)}$ on $[0,\infty)$, not a two-point supremum, so this statement is not an unfolding of the definition.
-- source:
--   Valizadeh, Gohari, Playing Games with Bounded Entropy: Convergence Rate and Approximate Equilibria, arXiv:1902.03676v1, p. 20, (18)–(19)

import Mathlib
import Definitions.Def_BoundedEntropyGames_ConvRate_Setting

namespace BoundedEntropyGames.ConvRate

/-- (18)–(19), p. 20: `J_cav(H(X|Y))` is attained by a two-point mixture of security levels
whose mixed entropy is at most `H(X|Y)`. -/
theorem eq_18_19 {𝒜 ℬ 𝒳 𝒴 : Type*} [Fintype 𝒜] [Nonempty 𝒜] [Fintype ℬ] [Nonempty ℬ]
    [Fintype 𝒳] [Fintype 𝒴] (u : 𝒜 → ℬ → ℝ) (pXY : 𝒳 × 𝒴 → ℝ) (hp : IsPMF pXY) :
    ∃ r ∈ Set.Icc (0 : ℝ) 1, ∃ p₁ ∈ stdSimplex ℝ 𝒜, ∃ p₂ ∈ stdSimplex ℝ 𝒜,
      r * U u p₁ + (1 - r) * U u p₂ = Jcav u (condEntropy pXY) ∧
      r * shannon p₁ + (1 - r) * shannon p₂ ≤ condEntropy pXY := by sorry

end BoundedEntropyGames.ConvRate
