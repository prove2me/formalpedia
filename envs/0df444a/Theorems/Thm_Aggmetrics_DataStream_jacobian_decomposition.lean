-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_jacobian_decomposition
-- name    : Aggmetrics.DataStream.jacobian_decomposition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:55:59.353081+00:00
-- url     : https://prove2.me/theorems/06874645-3190-43c9-a29d-902bbeef580a
-- title:
--   Data Stream: jacobian decomposition
-- statement:
--   Theorem, "Analytical Jacobian Drift Decomposition": for a composite metric
--   `M(t) = g(R11(t), R00(t), π(t))` built from a Fréchet-differentiable `g : ℝ × ℝ × ℝ → ℝ` and
--   differentiable canonical-coordinate/prior curves, the total temporal derivative is exactly the
--   multivariate chain rule, split along the paper's own grouping: the "concept drift" part (the
--   partials w.r.t. the two canonical coordinates `R11`, `R00`, each times its own rate of change)
--   plus the "prior shift" part (the partial w.r.t. `π`, times its rate of change). This is the
--   general chain rule (`HasFDerivAt.comp_hasDerivAt`) instantiated to `ℝ × ℝ × ℝ`, with the
--   three-way additive split obtained from linearity of the Fréchet derivative `g'` alone — no
--   extra hypothesis beyond differentiability of `g` and of the three coordinate curves is needed.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStream.lean#L194-L214
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStream.lean#L194-L214

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStream
set_option autoImplicit true
open Finset MeasureTheory
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.jacobian_decomposition
    (g : ℝ × ℝ × ℝ → ℝ) (R11 R00 π : ℝ → ℝ) (t : ℝ)
    (r11' r00' π' : ℝ)
    (hR11 : HasDerivAt R11 r11' t) (hR00 : HasDerivAt R00 r00' t) (hπ : HasDerivAt π π' t)
    (g' : ℝ × ℝ × ℝ →L[ℝ] ℝ) (hg : HasFDerivAt g g' (R11 t, R00 t, π t)) :
    HasDerivAt (fun s => g (R11 s, R00 s, π s))
      (g' (1, 0, 0) * r11' + g' (0, 1, 0) * r00' + g' (0, 0, 1) * π') t := by sorry
