-- Prove2me | Theorems.Thm_Auto_exp_sub_exp_neg
-- name    : Auto.exp_sub_exp_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:39:28.184906+00:00
-- url     : https://prove2.me/theorems/788ba777-3f7b-4730-8477-7b53517d298c
-- title:
--   Auto: exp sub exp neg
-- statement:
--   The Auto construction uses the exp sub exp neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L384-L389
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L384-L389

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

theorem Auto.exp_sub_exp_neg (θ : ℝ) :
    Complex.exp (θ * Complex.I) - Complex.exp ((-θ : ℝ) * Complex.I) =
      2 * Complex.I * (Real.sin θ : ℂ) := by sorry
