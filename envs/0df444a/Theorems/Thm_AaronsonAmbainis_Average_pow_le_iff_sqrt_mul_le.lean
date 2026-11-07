-- Prove2me | Theorems.Thm_AaronsonAmbainis_Average_pow_le_iff_sqrt_mul_le
-- name    : AaronsonAmbainis.Average.pow_le_iff_sqrt_mul_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:38:46.30824+00:00
-- url     : https://prove2.me/theorems/d76fe8b9-779d-49ae-b921-93df7ed16a61
-- title:
--   Average: pow le iff sqrt mul le
-- statement:
--   For `V, L, I ≥ 0`: `3 V^5 ≤ 3125 L² K^4 I²` if and only if `√15 V^{5/2} ≤ 125 L K² I`, where
--   `V^{5/2}` is written `V² · √V`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Average/Influence.lean#L168-L186
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Average/Influence.lean#L168-L186

import Definitions.Def_AaronsonAmbainis_Average_Iterate
import Definitions.Def_AaronsonAmbainis_Average_Influence
set_option autoImplicit true
open AaronsonAmbainis
open Finset
open AaronsonAmbainis.Average
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Average.pow_le_iff_sqrt_mul_le {V L K I : ℝ} (hV : 0 ≤ V) (hL : 0 ≤ L) (hI : 0 ≤ I) :
    3 * V ^ 5 ≤ 3125 * L ^ 2 * K ^ 4 * I ^ 2
      ↔ Real.sqrt 15 * (V ^ 2 * Real.sqrt V) ≤ 125 * L * K ^ 2 * I := by sorry
