-- Prove2me | Theorems.Thm_Eden_radialField_pos_between
-- name    : Eden.radialField_pos_between
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:29:07.634883+00:00
-- url     : https://prove2.me/theorems/4c483474-d7c1-5245-9956-c22c30599fae
-- title:
--   Eden: radial Field pos between
-- statement:
--   The Eden construction uses the radial Field pos between property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/RadialQualitative.lean#L36-L41
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/RadialQualitative.lean#L36-L41

import Definitions.Def_Eden_PhysicalRadius
import Definitions.Def_Eden_Uniqueness
import Definitions.Def_Eden_RadialQualitative
set_option autoImplicit true
noncomputable section
open Filter Set
open scoped Topology
open Eden

theorem Eden.radialField_pos_between {r : ℝ} (hr₁ : 1 < r) (hr₂ : r < Real.sqrt 2) :
    radialField r > 0 := by sorry
