-- Prove2me | Theorems.Thm_Experiments_NSA_eq_of_std_approx
-- name    : Experiments.NSA.eq_of_std_approx
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:54:23.679795+00:00
-- url     : https://prove2.me/theorems/f66e97ef-3fde-47e0-8571-c9d8cb0d2bb9
-- title:
--   NSA: eq of std approx
-- statement:
--   Standard points that are infinitely close are equal.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/Ultrapower.lean#L139-L140
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/Ultrapower.lean#L139-L140

import Mathlib
import Definitions.Def_Experiments_Ultrapower
set_option autoImplicit true
open Filter Set
open scoped Topology
noncomputable section
open Experiments Experiments.NSA
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

theorem Experiments.NSA.eq_of_std_approx {a b : E} (h : std a ≈ₕ std b) : a = b := by sorry
