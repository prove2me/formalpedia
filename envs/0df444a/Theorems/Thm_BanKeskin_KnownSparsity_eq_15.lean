-- Prove2me | Theorems.Thm_BanKeskin_KnownSparsity_eq_15
-- name    : BanKeskin.KnownSparsity.eq_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:02:13.302183+00:00
-- url     : https://prove2.me/theorems/09a9ceb6-c11b-49c9-a28f-6a25d1d2d939
-- title:
--   Equation (15), p. 5556 — experimental price variation grows as √t
-- statement:
--   Let $J_t=\sum_{k=1}^t\chi_k(p_k-\bar p_t)^2$, where $\chi_k$ selects experimental periods and $\bar p_t$ is the mean price on those periods. Under ILSX with distinct experimental prices $m_1$ and $m_2$, for every $t\ge5$,
--
--   $$J_t\ge\frac18(m_1-m_2)^2\sqrt t.$$
--
--   The bound supplies the deterministic amount of price variation used in the information and estimation-error estimates.
--
--   **Formalization Note** $J_t$ is computed from the fixed experimental prices and is therefore independent of the customer sample.
-- source:
--   Ban and Keskin, Personalized Dynamic Pricing with Machine Learning, Management Science 67(9) (2021), p. 5556, (13) and (15)

import Mathlib
import Definitions.Def_BanKeskin_KnownSparsity_Model

open MeasureTheory

namespace BanKeskin.KnownSparsity

/-- Price-variation growth (15), p. 5556. -/
theorem eq_15 {d : ℕ} {S : Finset (Fin (d + 1))} {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) (M : Model d S Ω P)
    (t : ℕ) (ht : 5 ≤ t) :
    (1 / 8 : ℝ) * (M.m1 - M.m2) ^ 2 * Real.sqrt (t : ℝ) ≤ M.J t := by sorry

end BanKeskin.KnownSparsity
