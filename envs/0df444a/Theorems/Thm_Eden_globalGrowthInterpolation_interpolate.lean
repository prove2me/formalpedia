-- Prove2me | Theorems.Thm_Eden_globalGrowthInterpolation_interpolate
-- name    : Eden.globalGrowthInterpolation_interpolate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:41:06.167656+00:00
-- url     : https://prove2.me/theorems/3c1b4129-4ec3-5031-a183-85fc796a516c
-- title:
--   Eden: global Growth Interpolation interpolate
-- statement:
--   The Eden construction uses the global Growth Interpolation interpolate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GlobalGrowthDimension.lean#L44-L51
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GlobalGrowthDimension.lean#L44-L51

import Definitions.Def_Eden_ExactGlobalGrowth
import Definitions.Def_Eden_LogarithmicInterpolation
import Definitions.Def_Eden_GlobalGrowthDimension
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.globalGrowthInterpolation_interpolate {c : ℝ} (hc : 4 ≤ c)
    {k : ℕ} (hk : k < 5) {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    globalGrowthInterpolation c ((k : ℝ) + α) =
      (1 - α) * globalGrowthRate c k + α * globalGrowthRate c (k + 1) := by sorry
