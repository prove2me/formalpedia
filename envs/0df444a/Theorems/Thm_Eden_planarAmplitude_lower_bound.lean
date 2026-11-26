-- Prove2me | Theorems.Thm_Eden_planarAmplitude_lower_bound
-- name    : Eden.planarAmplitude_lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:21:50.438796+00:00
-- url     : https://prove2.me/theorems/b6fea7c4-04b3-5bf4-bbae-3c21a70ecb3b
-- title:
--   Eden: planar Amplitude lower bound
-- statement:
--   The Eden construction uses the planar Amplitude lower bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FactorBounds.lean#L52-L55
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FactorBounds.lean#L52-L55

import Definitions.Def_Eden_InvariantSets
import Definitions.Def_Eden_GrowthRates
import Definitions.Def_Eden_SingularValues
import Definitions.Def_Eden_FactorBounds
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.planarAmplitude_lower_bound {t s : ℝ} (ht : 0 ≤ t)
    (hs₀ : 0 ≤ s) (hs₂ : s ≤ 2) : Real.exp (-2 * t) ≤ planarAmplitude t s := by sorry
