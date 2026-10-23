-- Prove2me | Theorems.Thm_FlexLearning_Threshold_piBarN_eq
-- name    : FlexLearning.Threshold.piBarN_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:25:53.437604+00:00
-- url     : https://prove2.me/theorems/95372230-c997-423e-bcfe-c71b401dc442
-- title:
--   Proof of Proposition 1, pp. A3–A4 — optimal static non-flexible profit π̄_N = 2(p−c)x + U(p−c)²/p
-- statement:
--   In the static two-product model with independent demands, each uniform on $[x, x+U]$ ($x \ge 0$, $U > 0$), price $p$ and dedicated unit cost $c$ with $0 \le c < p$, the optimal expected profit of the non-flexible system, $\bar\pi_N = \sup_{\mathbf Q \in \mathbb R^2_+} \pi_N(\mathbf Q)$, is
--   $$\bar\pi_N = 2(p-c)x + U\,\frac{(p-c)^2}{p}.$$
--
--   It is the right-hand side of the break-even equation (8) and enters every comparison in the proof of Proposition 1.
--
--   **Formalization Note** $U > 0$ and $0 \le c < p$ are added, as in the model.
-- source:
--   Chod, Markakis & Trichakis, On the Learning Benefits of Resource Flexibility, SSRN preprint 3212177 (version of December 6, 2019), pp. A3–A4 (PDF 36–37), proof of Proposition 1

import Mathlib
import Definitions.Def_FlexLearning_Threshold_Model

namespace FlexLearning.Threshold

theorem piBarN_eq (p c x U : ℝ) (hc : 0 ≤ c) (hcp : c < p) (hx : 0 ≤ x) (hU : 0 < U) :
    piBarN p c x U = 2 * (p - c) * x + U * ((p - c) ^ 2 / p) := by sorry

end FlexLearning.Threshold
