-- Prove2me | Theorems.Thm_Experiments_NSA_approx_zero_of_norm_le
-- name    : Experiments.NSA.approx_zero_of_norm_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:54:35.49299+00:00
-- url     : https://prove2.me/theorems/e4296461-7898-4cf7-9e2b-8fe87acaee7e
-- title:
--   NSA: approx zero of norm le
-- statement:
--   A finite multiple of an infinitesimal is infinitesimal.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/Ultrapower.lean#L143-L148
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/Ultrapower.lean#L143-L148

import Mathlib
import Definitions.Def_Experiments_Ultrapower
set_option autoImplicit true
open Filter Set
open scoped Topology
noncomputable section
open Experiments Experiments.NSA
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

theorem Experiments.NSA.approx_zero_of_norm_le {x : Hyp E} {y : Hyp F} {k : Hyp ℝ} {c : ℝ} (hk : k ≈ₕ std c)
    (hxy : ext norm x ≤ k * ext norm y) (hy : y ≈ₕ std 0) : x ≈ₕ std 0 := by sorry
