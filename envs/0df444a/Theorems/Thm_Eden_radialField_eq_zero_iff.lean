-- Prove2me | Theorems.Thm_Eden_radialField_eq_zero_iff
-- name    : Eden.radialField_eq_zero_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:29:05.63486+00:00
-- url     : https://prove2.me/theorems/e43e6fdc-2057-4a5f-92fc-2177b644c979
-- title:
--   Eden: radial Field eq zero iff
-- statement:
--   The Eden construction uses the radial Field eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/RadialQualitative.lean#L17-L28
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/RadialQualitative.lean#L17-L28

import Definitions.Def_Eden_PhysicalRadius
import Definitions.Def_Eden_Uniqueness
import Definitions.Def_Eden_RadialQualitative
set_option autoImplicit true
noncomputable section
open Filter Set
open scoped Topology
open Eden

theorem Eden.radialField_eq_zero_iff {r : ℝ} (hr : 0 ≤ r) :
    radialField r = 0 ↔ r = 0 ∨ r = 1 ∨ r = Real.sqrt 2 := by sorry
