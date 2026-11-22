-- Prove2me | Theorems.Thm_Auto_carlesonLin_mem
-- name    : Auto.carlesonLin_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T19:03:27.344092+00:00
-- url     : https://prove2.me/theorems/b875a802-75af-4ee1-b80b-0eed446c195b
-- title:
--   Auto: carleson Lin mem
-- statement:
--   The Auto construction uses the carleson Lin mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L1246-L1255
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L1246-L1255

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

theorem Auto.carlesonLin_mem (T : ℕ → ℝ → ℂ) (M : ℕ → ℝ) (lam : ℝ) (n : ℕ) (x : ℝ) :
    ∃ m ≤ n, carlesonLin T M lam n x = M m := by sorry
