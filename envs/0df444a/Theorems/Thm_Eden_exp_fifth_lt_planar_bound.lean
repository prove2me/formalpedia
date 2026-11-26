-- Prove2me | Theorems.Thm_Eden_exp_fifth_lt_planar_bound
-- name    : Eden.exp_fifth_lt_planar_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:26:56.314846+00:00
-- url     : https://prove2.me/theorems/5c8cee8a-9f71-5d3d-857e-22cede522ff8
-- title:
--   Eden: exp fifth lt planar bound
-- statement:
--   The Eden construction uses the exp fifth lt planar bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/VolumeConsequences.lean#L13-L15
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/VolumeConsequences.lean#L13-L15

import Definitions.Def_Eden_VolumeGrowth
import Definitions.Def_Eden_Uniqueness
import Definitions.Def_Eden_VolumeConsequences
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.exp_fifth_lt_planar_bound {c t : ℝ} (hc : 4 < c) (ht : 0 < t) :
    Real.exp (-c * t) < Real.exp (-4 * t) := by sorry
