-- Prove2me | Theorems.Thm_ActuarialValuation_deathYearIndicators_mul_eq_zero
-- name    : ActuarialValuation.deathYearIndicators_mul_eq_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T17:55:41.217288+00:00
-- url     : https://prove2.me/theorems/3e6a19b8-bd16-4552-b56e-0b032e7a8c72
-- title:
--   Different death-year indicators have zero product
-- statement:
--   Prove that indicators for distinct death years have zero product, removing cross-terms from the term assurance’s second moment.
--
--   **Mathematical statement**
--
--   $$
--   i\ne j\Longrightarrow\mathbf1_{D_i}(\omega)\mathbf1_{D_j}(\omega)=0
--   $$
-- source:
--   Chapter 3 §3.1.1 before equation (3.4), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html.

import Mathlib
import Definitions.Def_actuarial_deathYearEvent

namespace ActuarialValuation
theorem deathYearIndicators_mul_eq_zero {Ω : Type*} (K : Ω → ℕ)
    (i j : ℕ) (hij : i ≠ j) (ω : Ω)
    :
    (deathYearEvent K i).indicator (fun _ : Ω => (1 : ℝ)) ω *
      (deathYearEvent K j).indicator (fun _ : Ω => (1 : ℝ)) ω = 0 := by sorry
end ActuarialValuation
