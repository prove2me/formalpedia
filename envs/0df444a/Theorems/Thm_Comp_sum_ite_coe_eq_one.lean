-- Prove2me | Theorems.Thm_Comp_sum_ite_coe_eq_one
-- name    : Comp.sum_ite_coe_eq_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:06:38.209607+00:00
-- url     : https://prove2.me/theorems/1b18796b-a10e-467b-a695-096acdbbcee2
-- title:
--   Comp: sum ite coe eq one
-- statement:
--   The `q = 1` case, which is what a point-mass kernel needs.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L135-L137
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L135-L137

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_ModelData
set_option autoImplicit true
open Comp

theorem Comp.sum_ite_coe_eq_one {n t : ℕ} (ht : t < n) :
    ∑ s' : Fin n, (if (s' : ℕ) = t then (1 : ℚ) else 0) = 1 := by sorry
