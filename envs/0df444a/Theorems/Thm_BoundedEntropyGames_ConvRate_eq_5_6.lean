-- Prove2me | Theorems.Thm_BoundedEntropyGames_ConvRate_eq_5_6
-- name    : BoundedEntropyGames.ConvRate.eq_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:16:38.86727+00:00
-- url     : https://prove2.me/theorems/9b1f4b51-6dc7-454d-9857-528b6faaa593
-- title:
--   (5)–(6), p. 11 — second-order expansion of $H_\alpha(X|Y)$ around $\alpha=1$
-- statement:
--   Let $p_{XY}$ be a joint pmf on finite $\mathcal X\times\mathcal Y$. There is a constant $C\ge0$ (depending on $p_{XY}$) such that for every $\alpha\in[1/2,2]$ with $\alpha\ne1$,
--   $$
--   \big|H_\alpha(X|Y)-\big(H(X|Y)-d_1(X|Y)(\alpha-1)\big)\big|\le C(\alpha-1)^2 .
--   $$
--   In the paper's notation, $H_\alpha(X|Y)=H(X|Y)-d_1(X|Y)(\alpha-1)+R_{X|Y}(\alpha)$ with $|R_{X|Y}(\alpha)|\le d_2(X|Y)(\alpha-1)^2$.
--
--   This is the conditional counterpart of (3)–(4), used for the source side of the entropy-gap inequality (29).
--
--   **Formalization Note** $d_2(X|Y)$ is replaced by an existential constant $C$ depending only on $p_{XY}$. The paper's $d(p_{X|Y=y})$ in the formula for $d_1(X|Y)$ is read as $d_1(p_{X|Y=y})$, and its display (6) prints $|R_X(\alpha)|$ for $|R_{X|Y}(\alpha)|$; the statement uses the corrected readings.
-- source:
--   Valizadeh, Gohari, Playing Games with Bounded Entropy: Convergence Rate and Approximate Equilibria, arXiv:1902.03676v1, p. 11, §2.3, (5)–(6)

import Mathlib
import Definitions.Def_BoundedEntropyGames_ConvRate_Setting
import Definitions.Def_BoundedEntropyGames_ConvRate_Proof

namespace BoundedEntropyGames.ConvRate

/-- (5)–(6), p. 11: second-order expansion of `H_α(X|Y)` around `α = 1` on `[1/2, 2]`,
with the constant `d_2(X|Y)` replaced by an existential constant `C ≥ 0` depending on
`p_XY`. -/
theorem eq_5_6 {𝒳 𝒴 : Type*} [Fintype 𝒳] [Fintype 𝒴] (pXY : 𝒳 × 𝒴 → ℝ) (hp : IsPMF pXY) :
    ∃ C ≥ (0 : ℝ), ∀ α ∈ Set.Icc (1 / 2 : ℝ) 2, α ≠ 1 →
      |condRenyi α pXY - (condEntropy pXY - condD1 pXY * (α - 1))| ≤ C * (α - 1) ^ 2 := by sorry

end BoundedEntropyGames.ConvRate
