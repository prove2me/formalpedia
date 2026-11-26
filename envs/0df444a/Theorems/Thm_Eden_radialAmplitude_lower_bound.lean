-- Prove2me | Theorems.Thm_Eden_radialAmplitude_lower_bound
-- name    : Eden.radialAmplitude_lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:21:46.439634+00:00
-- url     : https://prove2.me/theorems/3624be7c-94ea-45e7-b7da-3636e0a6a21e
-- title:
--   Eden: radial Amplitude lower bound
-- statement:
--   The Eden construction uses the radial Amplitude lower bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FactorBounds.lean#L47-L50
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FactorBounds.lean#L47-L50

import Definitions.Def_Eden_InvariantSets
import Definitions.Def_Eden_GrowthRates
import Definitions.Def_Eden_SingularValues
import Definitions.Def_Eden_FactorBounds
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.radialAmplitude_lower_bound {t s : ℝ} (ht : 0 ≤ t)
    (hs₀ : 0 ≤ s) (hs₂ : s ≤ 2) : Real.exp (-4 * t) ≤ radialAmplitude t s := by sorry
