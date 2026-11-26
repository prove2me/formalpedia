-- Prove2me | Theorems.Thm_Eden_radial_excess_le
-- name    : Eden.radial_excess_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:15:50.266987+00:00
-- url     : https://prove2.me/theorems/7d0ed5fa-fce7-584d-b1fd-ca33dd9b8206
-- title:
--   Eden: radial excess le
-- statement:
--   The Eden construction uses the radial excess le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/UniformAttraction.lean#L26-L31
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/UniformAttraction.lean#L26-L31

import Definitions.Def_Eden_PhysicalRadius
import Definitions.Def_Eden_AttractorDistance
import Definitions.Def_Eden_StrictInvariance
import Definitions.Def_Eden_UniformAttraction
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden

theorem Eden.radial_excess_le {t r M : ℝ} (ht : 0 ≤ t) (hr : 0 ≤ r)
    (hrM : r ≤ M) (hM : Real.sqrt 2 ≤ M) :
    max (radiusEvolution t r - Real.sqrt 2) 0 ≤ radiusEvolution t M - Real.sqrt 2 := by sorry
