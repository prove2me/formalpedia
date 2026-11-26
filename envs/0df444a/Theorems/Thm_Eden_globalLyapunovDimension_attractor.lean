-- Prove2me | Theorems.Thm_Eden_globalLyapunovDimension_attractor
-- name    : Eden.globalLyapunovDimension_attractor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:25:52.829885+00:00
-- url     : https://prove2.me/theorems/1c1b29f1-76a2-5e40-b79f-9f2228456858
-- title:
--   Eden: global Lyapunov Dimension attractor
-- statement:
--   The global infimum over all real positive times equals the same attained
--   finite-time maximum. This is the Lyapunov dimension of the attractor.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FiniteTimeDimension.lean#L117-L131
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FiniteTimeDimension.lean#L117-L131

import Definitions.Def_Eden_SingularValueFunction
import Definitions.Def_Eden_VolumeGrowth
import Definitions.Def_Eden_FiniteTimeDimension
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.globalLyapunovDimension_attractor {c : ℝ} (hc : 4 < c) :
    globalLyapunovDimension c attractor = 4 + 4 / c := by sorry
