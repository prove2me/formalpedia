-- Prove2me | Theorems.Thm_FlexLearning_Threshold_piBarF_eq
-- name    : FlexLearning.Threshold.piBarF_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:25:58.711216+00:00
-- url     : https://prove2.me/theorems/dc6ecbd5-6c06-4da4-b254-8e0c29ebf7f6
-- title:
--   Proof of Proposition 1, p. A5 — optimal static flexible capacity Q̄_F(c_F) and profit π̄_F(c_F), branches p ≥ 2c_F and p < 2c_F
-- statement:
--   In the static model with independent demands uniform on $[x, x+U]$ ($x \ge 0$, $U > 0$), price $p$ and flexible unit cost $c_F$ with $0 \le c_F < p$, let $\bar\pi_F(c_F) = \sup_{Q_F \ge 0} \pi_F(c_F)(Q_F)$. Then:
--   1. if $p \ge 2c_F$, the capacity $\bar Q_{F,1}(c_F) = 2x + \big(2 - \sqrt{2c_F/p}\big)U$ attains the optimum and
--   $$\bar\pi_F(c_F) = 2(p-c_F)x + \tfrac23 c_F\Big(\sqrt{\tfrac{2c_F}{p}} - 3\Big)U + pU;$$
--   2. if $p < 2c_F$, the capacity $\bar Q_{F,2}(c_F) = 2x + \sqrt{2 - 2c_F/p}\;U$ attains the optimum and
--   $$\bar\pi_F(c_F) = 2(p-c_F)x + \tfrac23 (p-c_F)\sqrt{2 - \tfrac{2c_F}{p}}\;U.$$
--
--   These are the left-hand side of the break-even equation (8).
--
--   **Formalization Note** $U > 0$ and $0 \le c_F < p$ are added; they make the square roots real and the optimum interior or at the boundary as on the page.
-- source:
--   Chod, Markakis & Trichakis, On the Learning Benefits of Resource Flexibility, SSRN preprint 3212177 (version of December 6, 2019), p. A5 (PDF 38), proof of Proposition 1

import Mathlib
import Definitions.Def_FlexLearning_Threshold_Model

namespace FlexLearning.Threshold

theorem piBarF_eq (p x U cF : ℝ) (hcF : 0 ≤ cF) (hcFp : cF < p) (hx : 0 ≤ x) (hU : 0 < U) :
    (2 * cF ≤ p →
      piF p x U cF (2 * x + (2 - Real.sqrt (2 * cF / p)) * U) = piBarF p x U cF ∧
      piBarF p x U cF =
        2 * (p - cF) * x + 2 / 3 * cF * (Real.sqrt (2 * cF / p) - 3) * U + p * U) ∧
    (p < 2 * cF →
      piF p x U cF (2 * x + Real.sqrt (2 - 2 * cF / p) * U) = piBarF p x U cF ∧
      piBarF p x U cF = 2 * (p - cF) * x + 2 / 3 * (p - cF) * Real.sqrt (2 - 2 * cF / p) * U) := by sorry

end FlexLearning.Threshold
