-- Prove2me | Theorems.Thm_AaronsonAmbainis_Level_level_integration
-- name    : AaronsonAmbainis.Level.level_integration
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:18:42.266204+00:00
-- url     : https://prove2.me/theorems/fa1cc47b-2b9b-4cf0-8304-c4471cb3dce9
-- title:
--   Level: level integration
-- statement:
--   **Integration over the level.** If
--   `∑_i c_i (u_i - t)⁺ (t - v_i)⁺ ≤ ∑_k d_k 1_{[p_k, q_k)}(t)` for every real `t`, then
--   `∑_i c_i ((u_i - v_i)⁺)^3 / 6 ≤ ∑_k d_k (q_k - p_k)⁺`. No sign condition on `c`, `d`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Integral.lean#L128-L213
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Integral.lean#L128-L213

import Mathlib
import Definitions.Def_AaronsonAmbainis_Level_Integral
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset

theorem AaronsonAmbainis.Level.level_integration {α β : Type*} (s : Finset α) (r : Finset β)
    (c u v : α → ℝ) (d p q : β → ℝ)
    (h : ∀ t : ℝ, ∑ i ∈ s, c i * (max (u i - t) 0 * max (t - v i) 0)
        ≤ ∑ k ∈ r, d k * (if p k ≤ t ∧ t < q k then (1 : ℝ) else 0)) :
    ∑ i ∈ s, c i * (max (u i - v i) 0 ^ 3 / 6) ≤ ∑ k ∈ r, d k * max (q k - p k) 0 := by sorry
