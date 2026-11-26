-- Prove2me | Theorems.Thm_Eden_periodicGlobalGrowthInterpolation_interpolate
-- name    : Eden.periodicGlobalGrowthInterpolation_interpolate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:03:54.960432+00:00
-- url     : https://prove2.me/theorems/d8e0846e-2a26-5483-ab9c-5072d85b97fb
-- title:
--   Eden: periodic Global Growth Interpolation interpolate
-- statement:
--   Linear interpolation between every pair of consecutive global-sum nodes.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicGlobalDimension.lean#L47-L55
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicGlobalDimension.lean#L47-L55

import Definitions.Def_Eden_PeriodicGlobalGrowth
import Definitions.Def_Eden_PeriodicGlobalDimension
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.periodicGlobalGrowthInterpolation_interpolate {c : ℝ} (hc : 4 < c)
    {k : ℕ} (hk : k < 5) {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    periodicGlobalGrowthInterpolation c ((k : ℝ) + α) =
      (1 - α) * periodicGlobalGrowthRate c k + α * periodicGlobalGrowthRate c (k + 1) := by sorry
