-- Prove2me | Theorems.Thm_Experiments_NSA_approx_coe
-- name    : Experiments.NSA.approx_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:48:24.953985+00:00
-- url     : https://prove2.me/theorems/d439380d-7991-418f-b89d-062d7a1cfe13
-- title:
--   NSA: approx coe
-- statement:
--   For germs of sequences, `≈ₕ` is convergence of the difference along the ultrafilter.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/Ultrapower.lean#L102-L104
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/Ultrapower.lean#L102-L104

import Mathlib
import Definitions.Def_Experiments_Ultrapower
set_option autoImplicit true
open Filter Set
open scoped Topology
noncomputable section
open Experiments Experiments.NSA
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

theorem Experiments.NSA.approx_coe {u v : ℕ → E} :
    (u : Hyp E) ≈ₕ (v : Hyp E) ↔ Tendsto (fun n => u n - v n) (hyperfilter ℕ) (𝓝 0) := by sorry
