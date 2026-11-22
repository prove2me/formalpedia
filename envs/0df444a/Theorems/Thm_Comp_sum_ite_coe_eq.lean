-- Prove2me | Theorems.Thm_Comp_sum_ite_coe_eq
-- name    : Comp.sum_ite_coe_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:43:27.869804+00:00
-- url     : https://prove2.me/theorems/07b17bea-b622-4033-bc3e-947d10ca938d
-- title:
--   Comp: sum ite coe eq
-- statement:
--   A single weighted index in range contributes its weight to the sum and nothing elsewhere. The
--       arithmetic core of this file: `sum_denseOf` is this plus an induction, and a point-mass
--       kernel's well-formedness is this at `q = 1`.
--
--       `Fin.ext` is the fact that a `Fin` is determined by its value; it has gone under other names
--       (`Fin.eq_of_val_eq`, `Fin.val_injective`) in other versions.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L119-L132
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L119-L132

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_ModelData
set_option autoImplicit true
open Comp

theorem Comp.sum_ite_coe_eq {n t : ℕ} (ht : t < n) (q : ℚ) :
    ∑ s' : Fin n, (if (s' : ℕ) = t then q else 0) = q := by sorry
