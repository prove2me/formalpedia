-- Prove2me | Theorems.Thm_Auto_lt_norm_carlesonLin
-- name    : Auto.lt_norm_carlesonLin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T19:03:36.593783+00:00
-- url     : https://prove2.me/theorems/9fb28c2a-a49c-4061-91ca-74cc2bdb847d
-- title:
--   Auto: lt norm carleson Lin
-- statement:
--   The Auto construction uses the lt norm carleson Lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L1265-L1287
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L1265-L1287

module
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Definitions.Def_Triangular_Auto_Carleson
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal Convolution
noncomputable section
open Real

theorem Auto.lt_norm_carlesonLin {h : ℝ → ℂ} {M : ℕ → ℝ} {lam : ℝ} (n : ℕ) {x : ℝ}
    (hx : ∃ m ≤ n, lam < ‖carlesonOp h (fun _ => M m) x‖) :
    lam < ‖carlesonOp h (carlesonLin (fun m => carlesonOp h fun _ => M m) M lam n) x‖ := by sorry
