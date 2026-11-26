-- Prove2me | Theorems.Thm_Eden_globalGrowthInterpolation_integer
-- name    : Eden.globalGrowthInterpolation_integer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:49:37.036052+00:00
-- url     : https://prove2.me/theorems/66fc9be8-5b7c-5ae7-85aa-94f3f145b027
-- title:
--   Eden: global Growth Interpolation integer
-- statement:
--   The Eden construction uses the global Growth Interpolation integer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GlobalGrowthDimension.lean#L53-L58
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GlobalGrowthDimension.lean#L53-L58

import Definitions.Def_Eden_ExactGlobalGrowth
import Definitions.Def_Eden_LogarithmicInterpolation
import Definitions.Def_Eden_GlobalGrowthDimension
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.globalGrowthInterpolation_integer {c : ℝ} (hc : 4 ≤ c)
    {k : ℕ} (hk : k ≤ 5) :
    globalGrowthInterpolation c k = globalGrowthRate c k := by sorry
