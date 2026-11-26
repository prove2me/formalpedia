-- Prove2me | Theorems.Thm_Eden_singularValues_at_origin
-- name    : Eden.singularValues_at_origin
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:02:44.759796+00:00
-- url     : https://prove2.me/theorems/01dc34b6-d57a-4d7c-8fde-c63c6bf73c14
-- title:
--   Eden: singular Values at origin
-- statement:
--   The Eden construction uses the singular Values at origin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/OrderedStationarySpectrum.lean#L42-L53
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/OrderedStationarySpectrum.lean#L42-L53

import Definitions.Def_Eden_StationaryFactors
import Definitions.Def_Eden_SingularValues
import Mathlib.Data.List.Sort
import Mathlib.Order.Fin.Basic
import Definitions.Def_Eden_OrderedStationarySpectrum
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.singularValues_at_origin {c t : ℝ} (hc : 2 ≤ c) (ht : 0 ≤ t) :
    (fun i : Fin 5 => (fderiv ℝ (evolution c t) 0).toLinearMap.singularValues i) =
      ![Real.exp (-2 * t), Real.exp (-2 * t), Real.exp (-2 * t),
        Real.exp (-2 * t), Real.exp (-c * t)] := by sorry
