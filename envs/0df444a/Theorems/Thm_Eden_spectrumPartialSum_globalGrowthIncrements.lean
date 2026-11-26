-- Prove2me | Theorems.Thm_Eden_spectrumPartialSum_globalGrowthIncrements
-- name    : Eden.spectrumPartialSum_globalGrowthIncrements
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:40:50.77621+00:00
-- url     : https://prove2.me/theorems/902812a9-bb29-5eb9-93ce-b1a906c5f00a
-- title:
--   Eden: spectrum Partial Sum global Growth Increments
-- statement:
--   The Eden construction uses the spectrum Partial Sum global Growth Increments property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GlobalGrowthDimension.lean#L34-L42
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GlobalGrowthDimension.lean#L34-L42

import Definitions.Def_Eden_ExactGlobalGrowth
import Definitions.Def_Eden_LogarithmicInterpolation
import Definitions.Def_Eden_GlobalGrowthDimension
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.spectrumPartialSum_globalGrowthIncrements {c : ℝ} (hc : 4 ≤ c)
    {k : ℕ} (hk : k ≤ 5) :
    spectrumPartialSum (globalGrowthIncrements c) k = globalGrowthRate c k := by sorry
