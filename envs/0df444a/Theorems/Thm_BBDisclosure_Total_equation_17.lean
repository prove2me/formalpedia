-- Prove2me | Theorems.Thm_BBDisclosure_Total_equation_17
-- name    : BBDisclosure.Total.equation_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:24:05.085051+00:00
-- url     : https://prove2.me/theorems/99ec34a4-2df1-47f8-8d12-3c337ae5b09b
-- title:
--   (17), p. 8519 — BBD: symmetric equilibrium first-period price, share $\tfrac12$
-- statement:
--   Let $0<c<5/36$. In the two-period game with behavior-based disclosure, a symmetric subgame-perfect equilibrium exists, and in every one the common first-period price is
--
--   $$p^*_{a1}=p^*_{b1}=\frac43-\frac{c(5+54c)}{3\sqrt{1+12c}}+\frac{c(5+162c)}{3\sqrt{1+108c}},$$
--
--   and the first-period share at these prices is $x_1^*=\tfrac12$.
--
--   Compared with (9), this is the price behind Proposition 2.
--
--   **Formalization Note.** As for (9): deviations range over all nonnegative first-period prices, the second-period profile is an equilibrium at every share, the existence clause rules out vacuity, and $x_1^*=\tfrac12$ is Table 1's "First-period location".
-- source:
--   Zhang and Li, Retention or Acquisition? Behavior-Based Quality Disclosure, Management Sci. 71(10) (2025) 8510–8525, DOI 10.1287/mnsc.2022.01081, p. 8519, equation (17) and the sentence after it; Table 1, row First-period location (x*_1), p. 8517

import Mathlib
import Definitions.Def_BBDisclosure_Total_Stage2
import Definitions.Def_BBDisclosure_Total_Game

namespace BBDisclosure.Total

/-- (17), p. 8519, and Table 1's `x*_1 = 1/2`: under behavior-based disclosure a symmetric
subgame-perfect equilibrium exists, and in every one the first-period price is
`4/3 − c(5+54c)/(3√(1+12c)) + c(5+162c)/(3√(1+108c))` and the first-period share is `1/2`. -/
theorem equation_17 (c : ℝ) (hc0 : 0 < c) (hc : c < 5 / 36) :
    (∃ s : SPE_BBD, IsSymSPE_BBD c s) ∧
      ∀ s : SPE_BBD, IsSymSPE_BBD c s →
        s.pStar = 4 / 3 - c * (5 + 54 * c) / (3 * Real.sqrt (1 + 12 * c))
            + c * (5 + 162 * c) / (3 * Real.sqrt (1 + 108 * c)) ∧
          s.share s.pStar s.pStar = 1 / 2 := by sorry

end BBDisclosure.Total
