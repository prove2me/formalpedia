-- Prove2me | Theorems.Thm_BrandSpillover_Commitment_lemma_3
-- name    : BrandSpillover.Commitment.lemma_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T06:53:53.183422+00:00
-- url     : https://prove2.me/theorems/6d9aa41b-1679-4ea3-ab2b-ac05e9bfeb57
-- title:
--   Lemma 3, p. 13 — the CM's optimal wholesale prices under (O, O) with brand spillover
-- statement:
--   Assume the standing assumptions and let the spillover level in effect be $a \in [0,1]$; write $c^{oo}_1 = \tfrac12(2\theta - 1 - 3a(1-\theta))$ and $c^{oo}_2 = \tfrac12(1 + a(1-\theta))$. Under $(O,O)$, a price pair $(w_S, w_W)$ is optimal for the CM's program with the three participation constraints if and only if
--
--   $$w^{oo}_S = \min\Big\{c - \tfrac12 a(1-\theta),\ \tfrac12\Big\},\qquad
--   w^{oo}_W = \begin{cases} \min\big\{c + a(1-\theta),\ \tfrac14(2c + 2\theta - 1 + a(1-\theta))\big\} & \text{if } c \le c^{oo}_2,\\[2pt] \tfrac12(\theta + a(1-\theta)) & \text{if } c > c^{oo}_2.\end{cases}$$
--
--   In addition:
--
--   1. the first minimum equals $c - \tfrac12 a(1-\theta)$ if and only if $c \le c^{oo}_2$;
--   2. the second minimum equals $c + a(1-\theta)$ if and only if $c \le c^{oo}_1$.
--
--   With $a = \alpha$ this is the structure $(O, O)$ with brand spillover, and with $a = 0$ the structure without it; Proposition 4 compares Firm W's profits at the two.
-- source:
--   Wu, Zhang & Zhou, Brand Spillover as a Marketing Strategy, SSRN preprint 3891915 (June 2021), p. 13, Lemma 3, eqs. (1)–(3) (proof App. A, p. 32)

import Mathlib
import Definitions.Def_BrandSpillover_Commitment_Model

namespace BrandSpillover.Commitment

/-- Lemma 3, p. 13: under `(O, O)` with spillover level `a ∈ [0, 1]`, the CM's optimal prices are
`w^oo_S = min {c − a(1 − θ)/2, 1/2}` and, if `c ≤ c^oo_2`,
`w^oo_W = min {c + a(1 − θ), (2c + 2θ − 1 + a(1 − θ))/4}`, otherwise `w^oo_W = (θ + a(1 − θ))/2`;
the thresholds are `c^oo_2` for the first minimum and `c^oo_1` for the second. -/
theorem lemma_3 (P : Params) (hP : P.Standing) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (∀ w : ℝ × ℝ, IsOptPrices P a .OO w ↔
      (w.1 = min (P.c - 1 / 2 * a * (1 - P.θ)) (1 / 2) ∧
       w.2 = if P.c ≤ cOO2 P a then
               min (P.c + a * (1 - P.θ)) ((2 * P.c + 2 * P.θ - 1 + a * (1 - P.θ)) / 4)
             else (P.θ + a * (1 - P.θ)) / 2)) ∧
    (min (P.c - 1 / 2 * a * (1 - P.θ)) (1 / 2) = P.c - 1 / 2 * a * (1 - P.θ) ↔
      P.c ≤ cOO2 P a) ∧
    (min (P.c + a * (1 - P.θ)) ((2 * P.c + 2 * P.θ - 1 + a * (1 - P.θ)) / 4) =
        P.c + a * (1 - P.θ) ↔ P.c ≤ cOO1 P a) := by sorry

end BrandSpillover.Commitment
