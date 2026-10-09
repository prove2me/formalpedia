-- Prove2me | Theorems.Thm_ActuarialValuation_curtateSurvivalIndicators_mul
-- name    : ActuarialValuation.curtateSurvivalIndicators_mul
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T20:07:22.344744+00:00
-- url     : https://prove2.me/theorems/31f9b994-b267-4927-be85-98e52da51917
-- title:
--   Product of survival indicators is a later survival indicator
-- statement:
--   The product of two survival indicators records survival to the later of their dates. Indicators at different dates can both equal one, so they are neither mutually exclusive nor statistically independent in general.
--
--   **Mathematical statement**
--
--   $$
--   \mathbf1_{S_i}\mathbf1_{S_j}=\mathbf1_{S_{\max(i,j)}}
--   $$
-- source:
--   Derived from survival indicators in Chapter 3 §§3.1.1, 3.3.2, https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_curtateSurvivalEvent
open MeasureTheory

namespace ActuarialValuation

theorem curtateSurvivalIndicators_mul {Ω : Type*} (K : Ω → ℕ) (i j : ℕ) (ω : Ω)
    :
    (curtateSurvivalEvent K i).indicator (fun _ : Ω => (1 : ℝ)) ω *
      (curtateSurvivalEvent K j).indicator (fun _ : Ω => (1 : ℝ)) ω =
      (curtateSurvivalEvent K (max i j)).indicator (fun _ : Ω => (1 : ℝ)) ω := by sorry

end ActuarialValuation
