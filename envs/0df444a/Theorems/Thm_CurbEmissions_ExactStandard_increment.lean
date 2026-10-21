-- Prove2me | Theorems.Thm_CurbEmissions_ExactStandard_increment
-- name    : CurbEmissions.ExactStandard.increment
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:18:17.960956+00:00
-- url     : https://prove2.me/theorems/59c41ce9-7257-40da-bf82-5b52a24e4287
-- title:
--   Proof of Proposition 3, Online Appendix p. 13 (PDF 45) — the total-utility gain at s∗e is m2(2h1[ū+b(c−γ)]−(c−γ)ū)²/(8ū(c−γ)[4h1−(c−γ)])
-- statement:
--   Let the standing assumptions hold, let $s^*_e=\frac{2h_1[\bar u+b(c-\gamma)]-(c-\gamma)\bar u}{(c-\gamma)[4h_1-(c-\gamma)]}$, and let $s^*_{1D}$ be the split-market standard of Lemma A.1(1). Then the regulators' total utility at the exact global standard $s^*_e$ exceeds their total utility at the split-market configuration $(s^*_{1D},D)$ by
--   $$T_h(s^*_e)-\pi_1^D(s^*_{1D})-\pi_2^D(s^*_{1D})=\frac{m_2\big(2h_1[\bar u+b(c-\gamma)]-(c-\gamma)\bar u\big)^2}{8\bar u(c-\gamma)[4h_1-(c-\gamma)]}.$$
--   Moreover, if condition (1) of Lemma A.1 holds (for any value of $\bar x$), this increment is strictly positive.
--
--   The increment is the gain from negotiation that Proposition 3 needs to be positive.
--
--   **Formalization Note** The page asserts positivity "because $c\ge\gamma$ and $h_1\ge(c-\gamma)/2$", but the increment vanishes when $2h_1[\bar u+b(c-\gamma)]=(c-\gamma)\bar u$, for instance $b=0$, $h_1=(c-\gamma)/2$. Condition (1) excludes that case: $r>0$ together with $r$ at most the first term of condition (1) forces $(c-\gamma)\bar u<2h_1[\bar u+b(c-\gamma)]$. Positivity is therefore stated under condition (1).
-- source:
--   Han, Hu & Dawande, Curbing Emissions: Environmental Regulations and Product Offerings Across Markets, MSOM (authors' accepted manuscript, 2022-07-28), Online Appendix p. 13 (PDF 45), proof of Proposition 3

import Mathlib
import Definitions.Def_CurbEmissions_ExactStandard_Model

namespace CurbEmissions.ExactStandard

/-- Proof of Proposition 3, Online Appendix p. 13: the regulators' total utility at `s∗e` exceeds the
split-market total at `(s∗1D, D)` by `m2(2h1[ū + b(c−γ)] − (c−γ)ū)²/(8ū(c−γ)[4h1 − (c−γ)])`, and under
condition (1) this increment is positive. -/
theorem increment (P : Params) (hP : Standing P) :
    Th P ((2 * P.h1 * (P.ubar + P.b * (P.c - P.gam)) - (P.c - P.gam) * P.ubar) /
          ((P.c - P.gam) * (4 * P.h1 - (P.c - P.gam))))
        - pi1 P (s1DStar P) .D - pi2 P (s1DStar P) .D
      = P.m2 * (2 * P.h1 * (P.ubar + P.b * (P.c - P.gam)) - (P.c - P.gam) * P.ubar) ^ 2 /
          (8 * P.ubar * (P.c - P.gam) * (4 * P.h1 - (P.c - P.gam))) ∧
    ∀ xbar, Cond1 P xbar →
      0 < P.m2 * (2 * P.h1 * (P.ubar + P.b * (P.c - P.gam)) - (P.c - P.gam) * P.ubar) ^ 2 /
          (8 * P.ubar * (P.c - P.gam) * (4 * P.h1 - (P.c - P.gam))) := by sorry

end CurbEmissions.ExactStandard
