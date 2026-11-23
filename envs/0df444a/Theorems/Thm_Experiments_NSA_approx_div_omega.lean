-- Prove2me | Theorems.Thm_Experiments_NSA_approx_div_omega
-- name    : Experiments.NSA.approx_div_omega
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:55:03.262368+00:00
-- url     : https://prove2.me/theorems/bfd034d9-9956-401f-82d9-d7898f4557e2
-- title:
--   NSA: approx div omega
-- statement:
--   `c / (ω + 1)` is infinitesimal.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/Ultrapower.lean#L189-L191
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/Ultrapower.lean#L189-L191

import Mathlib
import Definitions.Def_Experiments_Ultrapower
set_option autoImplicit true
open Filter Set
open scoped Topology
noncomputable section
open Experiments Experiments.NSA
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

theorem Experiments.NSA.approx_div_omega (c : ℝ) : ext (fun n : ℕ => c / (n + 1 : ℝ)) ω ≈ₕ std 0 := by sorry
