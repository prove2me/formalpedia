-- Prove2me | Theorems.Thm_BoundedEntropyGames_ConvRate_eq_3_4
-- name    : BoundedEntropyGames.ConvRate.eq_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:16:28.68601+00:00
-- url     : https://prove2.me/theorems/c7d67b79-055e-4c5e-8aa1-4ba7bbb4ae60
-- title:
--   (3)–(4), pp. 10–11 — second-order expansion of $H_\alpha(X)$ around $\alpha=1$
-- statement:
--   Let $p$ be a pmf on a finite set. There is a constant $C\ge0$ (depending on $p$) such that for every $\alpha\in[1/2,2]$ with $\alpha\ne1$,
--   $$
--   \big|H_\alpha(p)-\big(H(p)-d_1(p)(\alpha-1)\big)\big|\le C(\alpha-1)^2 .
--   $$
--   In the paper's notation, $H_\alpha(X)=H(X)-d_1(X)(\alpha-1)+R_X(\alpha)$ with $|R_X(\alpha)|\le d_2(X)(\alpha-1)^2$.
--
--   The bound converts Rényi entropies near $\alpha=1$ into Shannon entropies in the entropy-gap inequality (29).
--
--   **Formalization Note** The paper's constant $d_2(X)=\frac12\max_{1/2\le\alpha'\le2}|H''_{\alpha'}(X)|$ is replaced by an existential constant $C$ in the same quantifier position (it depends only on $p$); the proof of Theorem 6 uses $d_2$ only as such a constant. The point $\alpha=1$ is excluded because the Rényi formula is not defined there (both sides tend to the same value).
-- source:
--   Valizadeh, Gohari, Playing Games with Bounded Entropy: Convergence Rate and Approximate Equilibria, arXiv:1902.03676v1, pp. 10–11, §2.3, (3)–(4)

import Mathlib
import Definitions.Def_BoundedEntropyGames_ConvRate_Setting
import Definitions.Def_BoundedEntropyGames_ConvRate_Proof

namespace BoundedEntropyGames.ConvRate

/-- (3)–(4), pp. 10–11: second-order expansion of `H_α(X)` around `α = 1` on `[1/2, 2]`,
with the constant `d_2(X)` replaced by an existential constant `C ≥ 0` depending on `p_X`. -/
theorem eq_3_4 {𝒳 : Type*} [Fintype 𝒳] (p : 𝒳 → ℝ) (hp : IsPMF p) :
    ∃ C ≥ (0 : ℝ), ∀ α ∈ Set.Icc (1 / 2 : ℝ) 2, α ≠ 1 →
      |renyi α p - (shannon p - d1 p * (α - 1))| ≤ C * (α - 1) ^ 2 := by sorry

end BoundedEntropyGames.ConvRate
