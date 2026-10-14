-- Prove2me | Theorems.Thm_BBDisclosure_Total_proposition_2
-- name    : BBDisclosure.Total.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:24:21.165831+00:00
-- url     : https://prove2.me/theorems/f2c3ffd2-fb6a-4b32-99ff-817147e2af98
-- title:
--   Proposition 2, p. 8520 — a cutoff $c_h$ for first-period prices and profits
-- statement:
--   There is a cutoff $c_h\in(0,5/36)$ with the following property. For every unit disclosure cost $0<c<5/36$, every symmetric subgame-perfect equilibrium of the two-period game under uniform disclosure, and every symmetric subgame-perfect equilibrium under behavior-based disclosure (BBD):
--   1. if $c>c_h$, the BBD first-period price is higher than the uniform one, and so are both firms' first-period profits;
--   2. if $c<c_h$, the BBD first-period price is lower, and so are both firms' first-period profits.
--
--   In symbols, writing $p^{*}$ and $p^*x_1^*$, $p^*(1-x_1^*)$ for the equilibrium price and first-period profits,
--   $$c>c_h\Rightarrow p^{*,U}<p^{*,BBD},\qquad c<c_h\Rightarrow p^{*,BBD}<p^{*,U}.$$
--
--   The result says that the effect of BBD on first-period competition reverses with the disclosure cost.
--
--   **Formalization Note.** The cutoff is fixed before $c$ and before the equilibria, and lies strictly inside $(0,5/36)$, so both directions have content; nothing is claimed at $c=c_h$. The paper gives no value of $c_h$ (Online Appendix). Firm B's first-period profit is included by the symmetry the paper invokes.
-- source:
--   Zhang and Li, Retention or Acquisition? Behavior-Based Quality Disclosure, Management Sci. 71(10) (2025) 8510–8525, DOI 10.1287/mnsc.2022.01081, p. 8520, Proposition 2

import Mathlib
import Definitions.Def_BBDisclosure_Total_Stage2
import Definitions.Def_BBDisclosure_Total_Game

namespace BBDisclosure.Total

/-- Proposition 2, p. 8520: there is a cutoff `c_h ∈ (0, 5/36)` such that, relative to uniform
disclosure, behavior-based disclosure raises the first-period price and both firms' first-period
profits when `c > c_h`, and lowers them when `c < c_h`. -/
theorem proposition_2 :
    ∃ ch : ℝ, 0 < ch ∧ ch < 5 / 36 ∧
      ∀ c : ℝ, 0 < c → c < 5 / 36 →
        ∀ (sU : SPE_U) (sB : SPE_BBD), IsSymSPE_U c sU → IsSymSPE_BBD c sB →
          (ch < c → sU.pStar < sB.pStar ∧ firstProfitA_U sU < firstProfitA_BBD sB ∧
              firstProfitB_U sU < firstProfitB_BBD sB) ∧
          (c < ch → sB.pStar < sU.pStar ∧ firstProfitA_BBD sB < firstProfitA_U sU ∧
              firstProfitB_BBD sB < firstProfitB_U sU) := by sorry

end BBDisclosure.Total
