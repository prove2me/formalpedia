-- Prove2me | Theorems.Thm_Experiments_NSA_approx_std_coe
-- name    : Experiments.NSA.approx_std_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:48:29.068514+00:00
-- url     : https://prove2.me/theorems/b3f1dbd4-5d11-43b1-bd9b-4f34a3bcad7d
-- title:
--   NSA: approx std coe
-- statement:
--   The germ of `u` is infinitely close to `a` exactly when `u` tends to `a` along the
--   ultrafilter: `a` is the standard part of `u`.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/Ultrapower.lean#L108-L110
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/Ultrapower.lean#L108-L110

import Mathlib
import Definitions.Def_Experiments_Ultrapower
set_option autoImplicit true
open Filter Set
open scoped Topology
noncomputable section
open Experiments Experiments.NSA
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

theorem Experiments.NSA.approx_std_coe {u : ℕ → E} {a : E} :
    (u : Hyp E) ≈ₕ std a ↔ Tendsto u (hyperfilter ℕ) (𝓝 a) := by sorry
