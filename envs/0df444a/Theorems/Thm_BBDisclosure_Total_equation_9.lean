-- Prove2me | Theorems.Thm_BBDisclosure_Total_equation_9
-- name    : BBDisclosure.Total.equation_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:24:04.523496+00:00
-- url     : https://prove2.me/theorems/9719b1e5-5e3f-4a95-b9bd-08bd15697c07
-- title:
--   (9), p. 8517 — uniform disclosure: symmetric equilibrium price $p^*_{a1}=p^*_{b1}=\tfrac23(2-c+c/\sqrt{1+27c})$, share $\tfrac12$
-- statement:
--   Let $0<c<5/36$. In the two-period game with uniform disclosure, a symmetric subgame-perfect equilibrium exists, and in every symmetric subgame-perfect equilibrium the common first-period price is
--
--   $$p^*_{a1}=p^*_{b1}=\frac23\Big(2-c+\frac{c}{\sqrt{1+27c}}\Big),$$
--
--   and the first-period share at these prices is $x_1^*=\tfrac12$.
--
--   This is the benchmark first-period outcome against which Proposition 2 compares behavior-based disclosure.
--
--   **Formalization Note.** The equilibrium is global: no deviation to any nonnegative first-period price is profitable, including deviations that move the share into regions 2 or 3 (the paper verifies these in its Online Appendix). The share $x_1^*=\tfrac12$ is Table 1's "First-period location", p. 8517. The existence clause is part of the statement so that the universal clause is not vacuous; "we obtain" is read as determining the price in every symmetric equilibrium.
-- source:
--   Zhang and Li, Retention or Acquisition? Behavior-Based Quality Disclosure, Management Sci. 71(10) (2025) 8510–8525, DOI 10.1287/mnsc.2022.01081, p. 8517, equation (9) and the sentence after it; Table 1, row First-period location (x*_1)

import Mathlib
import Definitions.Def_BBDisclosure_Total_Stage2
import Definitions.Def_BBDisclosure_Total_Game

namespace BBDisclosure.Total

/-- (9), p. 8517, and Table 1's `x*_1 = 1/2`: under uniform disclosure a symmetric subgame-perfect
equilibrium exists, and in every one the first-period price is `(2/3)(2 − c + c/√(1+27c))` and the
first-period share is `1/2`. -/
theorem equation_9 (c : ℝ) (hc0 : 0 < c) (hc : c < 5 / 36) :
    (∃ s : SPE_U, IsSymSPE_U c s) ∧
      ∀ s : SPE_U, IsSymSPE_U c s →
        s.pStar = 2 / 3 * (2 - c + c / Real.sqrt (1 + 27 * c)) ∧
          s.share s.pStar s.pStar = 1 / 2 := by sorry

end BBDisclosure.Total
