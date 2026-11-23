-- Prove2me | Theorems.Thm_Comp_sum_denseOf
-- name    : Comp.sum_denseOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:48:07.045919+00:00
-- url     : https://prove2.me/theorems/d83df415-0846-4253-9409-9cb482665fc8
-- title:
--   Comp: sum dense Of
-- statement:
--   **The payoff of the sparse form.** The densified vector sums to the list's own total, provided
--       every key is a real state. An induction on the list, with `sum_ite_coe_eq` at each step.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L154-L165
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L154-L165

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_ModelData
set_option autoImplicit true
open Comp

theorem Comp.sum_denseOf (n : ℕ) (dist : List (ℕ × ℚ)) :
    (∀ p ∈ dist, p.1 < n) →
      ∑ s' : Fin n, denseOf n dist s' = (dist.map Prod.snd).sum := by sorry
