-- Prove2me | Theorems.Thm_BrandSpillover_Commitment_lemma_1
-- name    : BrandSpillover.Commitment.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:53:50.801745+00:00
-- url     : https://prove2.me/theorems/4c38e843-d3ef-4c03-b4f4-d26e23cf1168
-- title:
--   Lemma 1, p. 11 — the CM never prefers the sourcing structure (I, I) or (I, O)
-- statement:
--   Assume the standing assumptions $c > 0$, $\underline\theta \le \theta < 1$, $\alpha \in [0,1]$, and let $a$ be any spillover level. Then:
--
--   1. every optimal solution of the CM's $(I,O)$ program gives the CM strictly less than every optimal solution of its $(O,I)$ program;
--   2. the CM's profit under $(I,I)$, which is $0$, is strictly less than its profit at every optimal solution of the $(O,I)$ program;
--   3. consequently every equilibrium sourcing structure is $(O,O)$ or $(O,I)$:
--
--   $$\text{equilibrium } (s, w) \;\Longrightarrow\; s \in \{(O,O),\,(O,I)\}.$$
--
--   The lemma reduces the CM's choice to two structures, which is the starting point of the equilibrium analysis.
-- source:
--   Wu, Zhang & Zhou, Brand Spillover as a Marketing Strategy, SSRN preprint 3891915 (June 2021), p. 11, Lemma 1 (proof App. A, p. 31)

import Mathlib
import Definitions.Def_BrandSpillover_Commitment_Model

namespace BrandSpillover.Commitment

/-- Lemma 1, p. 11 (proof App. A, p. 31): the CM never prefers `(I, I)` or `(I, O)`. Every
optimum of the `(I, O)` program and the `(I, I)` outcome give the CM strictly less than every
optimum of the `(O, I)` program, so every equilibrium structure is `(O, O)` or `(O, I)`. -/
theorem lemma_1 (P : Params) (hP : P.Standing) (a : ℝ) :
    (∀ w w' : ℝ × ℝ, IsOptPrices P a .IO w → IsOptPrices P a .OI w' →
        cmProfit P a .IO w < cmProfit P a .OI w') ∧
    (∀ w w' : ℝ × ℝ, IsOptPrices P a .OI w' → cmProfit P a .II w < cmProfit P a .OI w') ∧
    (∀ (s : Structure) (w : ℝ × ℝ), IsEquilibrium P a s w → s = .OO ∨ s = .OI) := by sorry

end BrandSpillover.Commitment
