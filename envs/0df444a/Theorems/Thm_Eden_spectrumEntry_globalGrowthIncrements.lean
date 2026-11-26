-- Prove2me | Theorems.Thm_Eden_spectrumEntry_globalGrowthIncrements
-- name    : Eden.spectrumEntry_globalGrowthIncrements
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:41:10.505478+00:00
-- url     : https://prove2.me/theorems/a8d8967a-2e42-4f12-a876-1dba33aee12b
-- title:
--   Eden: spectrum Entry global Growth Increments
-- statement:
--   The Eden construction uses the spectrum Entry global Growth Increments property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GlobalGrowthDimension.lean#L29-L32
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GlobalGrowthDimension.lean#L29-L32

import Definitions.Def_Eden_ExactGlobalGrowth
import Definitions.Def_Eden_LogarithmicInterpolation
import Definitions.Def_Eden_GlobalGrowthDimension
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.spectrumEntry_globalGrowthIncrements (c : ℝ) {k : ℕ} (hk : k < 5) :
    spectrumEntry (globalGrowthIncrements c) k =
      globalGrowthRate c (k + 1) - globalGrowthRate c k := by sorry
