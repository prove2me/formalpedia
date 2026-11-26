-- Prove2me | Theorems.Thm_Eden_finiteTimeDimension_lt_target_of_not_mem_torus
-- name    : Eden.finiteTimeDimension_lt_target_of_not_mem_torus
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:02:01.432276+00:00
-- url     : https://prove2.me/theorems/9765d20f-8b11-48e9-a807-b20eaf390240
-- title:
--   Eden: finite Time Dimension lt target of not mem torus
-- statement:
--   The Eden construction uses the finite Time Dimension lt target of not mem torus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FiniteTimeDimension.lean#L92-L96
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FiniteTimeDimension.lean#L92-L96

import Definitions.Def_Eden_SingularValueFunction
import Definitions.Def_Eden_VolumeGrowth
import Definitions.Def_Eden_FiniteTimeDimension
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.finiteTimeDimension_lt_target_of_not_mem_torus {c t : ℝ}
    (hc : 4 < c) (ht : 0 < t) {p : PhaseSpace} (hp : p ∈ attractor) (hT : p ∉ torus) :
    finiteTimeDimension c t p < targetDimension c := by sorry
