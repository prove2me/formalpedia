-- Prove2me | Theorems.Thm_Eden_planar_factors_product
-- name    : Eden.planar_factors_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:23:23.616714+00:00
-- url     : https://prove2.me/theorems/096a7af4-e8b7-511b-9c53-2b00f6cb9b96
-- title:
--   Eden: planar factors product
-- statement:
--   The Eden construction uses the planar factors product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/VolumeGrowth.lean#L74-L77
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/VolumeGrowth.lean#L74-L77

import Definitions.Def_Eden_FactorBounds
import Definitions.Def_Eden_VolumeGrowth
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.planar_factors_product {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    radialAmplitude t s * planarAmplitude t s = Real.exp (2 * t - 6 * radialDefect t s) := by sorry
