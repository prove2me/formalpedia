-- Prove2me | Theorems.Thm_BrandSpillover_Commitment_lemma_2
-- name    : BrandSpillover.Commitment.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:53:51.655738+00:00
-- url     : https://prove2.me/theorems/8cd74964-5f26-46f0-9814-150b8f9555c1
-- title:
--   Lemma 2, p. 12 — under (O, I) the CM's optimal wholesale price is min{c, (2 − θ + c)/4}
-- statement:
--   Assume the standing assumptions. Under the sourcing structure $(O,I)$, a wholesale price $w_S$ is optimal for the CM's program (maximize $w_S q^{oi}_S$ subject to Firm S's participation constraint $\Pi^{oi}_S(w_S) \ge \Pi^{ii}_S$) if and only if
--
--   $$w^{oi}_S = \min\Big\{c,\ \tfrac14(2 - \theta + c)\Big\}.$$
--
--   Moreover, the minimum equals $c$ exactly when $c \le c^{oi} = \tfrac13(2-\theta)$; otherwise it is $\tfrac14(2-\theta+c)$.
--
--   The price determines Firm W's profit when the CM induces $(O,I)$, which is the case of Proposition 4(i).
--
--   **Formalization Note** The price to Firm W is irrelevant under $(O,I)$ and is left unconstrained. The statement holds for any spillover level, which plays no role under $(O,I)$.
-- source:
--   Wu, Zhang & Zhou, Brand Spillover as a Marketing Strategy, SSRN preprint 3891915 (June 2021), p. 12, Lemma 2 (proof App. A, p. 32)

import Mathlib
import Definitions.Def_BrandSpillover_Commitment_Model

namespace BrandSpillover.Commitment

/-- Lemma 2, p. 12: under `(O, I)` the CM's optimal wholesale price is
`w^oi_S = min {c, (2 − θ + c)/4}`, and the minimum is `c` exactly when `c ≤ c^oi = (2 − θ)/3`. -/
theorem lemma_2 (P : Params) (hP : P.Standing) (a : ℝ) :
    (∀ w : ℝ × ℝ, IsOptPrices P a .OI w ↔ w.1 = min P.c ((2 - P.θ + P.c) / 4)) ∧
    (min P.c ((2 - P.θ + P.c) / 4) = P.c ↔ P.c ≤ cOI P) := by sorry

end BrandSpillover.Commitment
