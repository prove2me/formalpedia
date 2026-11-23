-- Prove2me | Theorems.Thm_Experiments_NSA_approx_of_le_of_le
-- name    : Experiments.NSA.approx_of_le_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:54:32.178317+00:00
-- url     : https://prove2.me/theorems/07819481-cd72-4b32-a8e7-e1bbff880785
-- title:
--   NSA: approx of le of le
-- statement:
--   Squeeze: a hyperreal between two that are infinitely close to `t` is too.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/Ultrapower.lean#L151-L156
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/Ultrapower.lean#L151-L156

import Mathlib
import Definitions.Def_Experiments_Ultrapower
set_option autoImplicit true
open Filter Set
open scoped Topology
noncomputable section
open Experiments Experiments.NSA
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

theorem Experiments.NSA.approx_of_le_of_le {lo ξ hi : Hyp ℝ} {t : ℝ} (hlo : lo ≤ ξ) (hhi : ξ ≤ hi)
    (hlot : lo ≈ₕ std t) (hhit : hi ≈ₕ std t) : ξ ≈ₕ std t := by sorry
