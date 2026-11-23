-- Prove2me | Theorems.Thm_Comp_add_ne_zero_iff_of_nonneg
-- name    : Comp.add_ne_zero_iff_of_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:48:29.719076+00:00
-- url     : https://prove2.me/theorems/28ff5238-fb20-4ec3-b6cb-f3f0aa899330
-- title:
--   Comp: add ne zero iff of nonneg
-- statement:
--   A sum of two nonnegative rationals vanishes only if both do, so it is nonzero exactly when one
--       of them is. The only arithmetic `denseOf_ne_zero_iff` needs, and the reason nonnegativity is a
--       hypothesis there: with cancellation allowed, a support could not be read off the keys.
--       (`Comp/HideOrRunQ.lean`'s `half_add_half_ne_zero` is this fact with explicit `1/2`s.)
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L176-L192
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L176-L192

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_ModelData
set_option autoImplicit true
open Comp

theorem Comp.add_ne_zero_iff_of_nonneg {a b : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a + b ≠ 0 ↔ a ≠ 0 ∨ b ≠ 0 := by sorry
