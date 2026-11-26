-- Prove2me | Theorems.Thm_Eden_radialField_neg_above
-- name    : Eden.radialField_neg_above
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:29:13.330256+00:00
-- url     : https://prove2.me/theorems/c63396ab-7deb-46ce-b524-344845be22d0
-- title:
--   Eden: radial Field neg above
-- statement:
--   The Eden construction uses the radial Field neg above property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/RadialQualitative.lean#L43-L49
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/RadialQualitative.lean#L43-L49

import Definitions.Def_Eden_PhysicalRadius
import Definitions.Def_Eden_Uniqueness
import Definitions.Def_Eden_RadialQualitative
set_option autoImplicit true
noncomputable section
open Filter Set
open scoped Topology
open Eden

theorem Eden.radialField_neg_above {r : ℝ} (hr : Real.sqrt 2 < r) :
    radialField r < 0 := by sorry
