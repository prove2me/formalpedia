-- Prove2me | Theorems.Thm_Eden_log_planar_factors
-- name    : Eden.log_planar_factors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:23:19.434798+00:00
-- url     : https://prove2.me/theorems/250e5bea-9a01-5691-8307-f229e0f2a090
-- title:
--   Eden: log planar factors
-- statement:
--   The Eden construction uses the log planar factors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/VolumeGrowth.lean#L55-L72
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/VolumeGrowth.lean#L55-L72

import Definitions.Def_Eden_FactorBounds
import Definitions.Def_Eden_VolumeGrowth
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.log_planar_factors {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    Real.log (radialAmplitude t s) + Real.log (planarAmplitude t s) =
      2 * t - 6 * radialDefect t s := by sorry
