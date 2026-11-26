-- Prove2me | Theorems.Thm_Eden_squaredRadiusEvolution_eq_self_iff
-- name    : Eden.squaredRadiusEvolution_eq_self_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:42:27.160599+00:00
-- url     : https://prove2.me/theorems/16019d93-f6f1-5827-bd3d-d6f8a74672c3
-- title:
--   Eden: squared Radius Evolution eq self iff
-- statement:
--   At positive time, the only fixed initial squared radii are 0, 1 and 2.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/RadialReturns.lean#L17-L47
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/RadialReturns.lean#L17-L47

import Definitions.Def_Eden_InvariantSets
import Definitions.Def_Eden_StationaryFactors
import Definitions.Def_Eden_RadialReturns
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.squaredRadiusEvolution_eq_self_iff {t s : ℝ} (ht : 0 < t) :
    squaredRadiusEvolution t s = s ↔ s = 0 ∨ s = 1 ∨ s = 2 := by sorry
