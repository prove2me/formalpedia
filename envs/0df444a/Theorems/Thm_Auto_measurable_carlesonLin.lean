-- Prove2me | Theorems.Thm_Auto_measurable_carlesonLin
-- name    : Auto.measurable_carlesonLin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T19:03:29.438388+00:00
-- url     : https://prove2.me/theorems/bc4a2529-13b2-4d8c-ba9d-8d380b45255b
-- title:
--   Auto: measurable carleson Lin
-- statement:
--   The Auto construction uses the measurable carleson Lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L1257-L1263
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L1257-L1263

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

theorem Auto.measurable_carlesonLin {T : ℕ → ℝ → ℂ} (hT : ∀ n, Measurable (T n)) (M : ℕ → ℝ)
    (lam : ℝ) (n : ℕ) : Measurable (carlesonLin T M lam n) := by sorry
