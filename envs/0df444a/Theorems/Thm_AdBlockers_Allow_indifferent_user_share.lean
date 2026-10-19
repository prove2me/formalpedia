-- Prove2me | Theorems.Thm_AdBlockers_Allow_indifferent_user_share
-- name    : AdBlockers.Allow.indifferent_user_share
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:15:44.399543+00:00
-- url     : https://prove2.me/theorems/a96be7b0-923e-4d72-bdc6-6ca0223c24a5
-- title:
--   Proof of Proposition 1, case 1 — the users preferring platform 1 have measure equal to the clipped Hotelling share
-- statement:
--   Let $m, d_1, d_2 \in \mathbb{R}$. A user at position $x \in [0,1]$ of the Hotelling line gets utility $m + (1-x) - d_1$ from platform 1 and $m + x - d_2$ from platform 2. Then the set of users who strictly prefer platform 1 has Lebesgue measure equal to the clipped Hotelling share:
--   $$
--   \operatorname{Leb}\big\{x \in [0,1] : m + x - d_2 < m + (1 - x) - d_1\big\} \;=\; \max\Big\{0, \min\Big\{1, \frac{1 + d_2 - d_1}{2}\Big\}\Big\}.
--   $$
--
--   This identifies the share used throughout the model with the paper's indifferent user $x_N = (1 + d_2 - d_1)/2$, including the cases where the indifferent user lies outside $[0,1]$ and one platform takes the whole segment.
--
--   **Formalization Note** The measure is the Lebesgue measure `volume` on $\mathbb{R}$, valued in $[0,\infty]$, and the right-hand side is embedded with `ENNReal.ofReal`.
-- source:
--   Despotakis, Ravi & Srinivasan, The Beneficial Effects of Ad Blockers, SSRN 3083119 (version of Nov. 28, 2017), p. 40, proof of Proposition 1 (Appendix A.1), case 1 (indifferent user x_N)

import Mathlib
import Definitions.Def_AdBlockers_Allow_Duopoly

namespace AdBlockers.Allow

open MeasureTheory

/-- Proof of Proposition 1 (Appendix A.1), case 1, p. 40: for every intrinsic value `m` and all
disutilities `d₁, d₂`, the users on `[0, 1]` who strictly prefer platform 1
(`m + (1 - x) - d₁ > m + x - d₂`) form a set of Lebesgue measure `hotellingShare d₁ d₂`. -/
theorem indifferent_user_share (m d₁ d₂ : ℝ) :
    volume {x : ℝ | x ∈ Set.Icc (0 : ℝ) 1 ∧ m + x - d₂ < m + (1 - x) - d₁} =
      ENNReal.ofReal (hotellingShare d₁ d₂) := by sorry

end AdBlockers.Allow
