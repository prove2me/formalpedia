-- Prove2me | Theorems.Thm_Experiments_NSA_approx_slope_of_hasDerivAt
-- name    : Experiments.NSA.approx_slope_of_hasDerivAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:54:46.200981+00:00
-- url     : https://prove2.me/theorems/5315858d-82f4-4150-b9d8-09869422c003
-- title:
--   NSA: approx slope of has Deriv At
-- statement:
--   Derivative: difference quotients over positive infinitesimals are infinitely close to it.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/Ultrapower.lean#L180-L186
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/Ultrapower.lean#L180-L186

import Mathlib
import Definitions.Def_Experiments_Ultrapower
set_option autoImplicit true
open Filter Set
open scoped Topology
noncomputable section
open Experiments Experiments.NSA
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

theorem Experiments.NSA.approx_slope_of_hasDerivAt [NormedSpace ℝ E] {f : ℝ → E} {f' : E} {x : ℝ}
    (hf : HasDerivAt f f' x) {ε : Hyp ℝ} (hpos : IMem ε (Ioi 0)) (hε : ε ≈ₕ std 0) :
    ext (fun h => h⁻¹ • (f (x + h) - f x)) ε ≈ₕ std f' := by sorry
