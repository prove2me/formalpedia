-- Prove2me | Theorems.Thm_Comp_denseOf_nonneg
-- name    : Comp.denseOf_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:43:24.02461+00:00
-- url     : https://prove2.me/theorems/ed029dbc-cc2c-4f93-85cc-b03ddad86eab
-- title:
--   Comp: dense Of nonneg
-- statement:
--   A sparse distribution with nonnegative weights densifies to a nonnegative vector.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L140-L150
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L140-L150

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_ModelData
set_option autoImplicit true
open Comp

theorem Comp.denseOf_nonneg (n : ℕ) (dist : List (ℕ × ℚ)) (s' : Fin n) :
    (∀ p ∈ dist, 0 ≤ p.2) → 0 ≤ denseOf n dist s' := by sorry
