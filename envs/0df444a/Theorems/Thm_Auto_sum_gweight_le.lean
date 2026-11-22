-- Prove2me | Theorems.Thm_Auto_sum_gweight_le
-- name    : Auto.sum_gweight_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:51:42.757912+00:00
-- url     : https://prove2.me/theorems/3936ff4a-5b53-47f6-a9b2-a8c345192e44
-- title:
--   Auto: sum gweight le
-- statement:
--   The Auto construction uses the sum gweight le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L5419-L5535
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L5419-L5535

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
open Auto
noncomputable section

theorem Auto.sum_gweight_le {ι : Type*} [Fintype ι] (u : ι → ℝ) {h σ : ℝ} (hh : 0 < h)
    (hσ : h ^ 2 ≤ σ) (kk : ι → ℤ) (hk : Function.Injective kk) (hu : ∀ i, u i = h * kk i)
    (p : ℝ) :
    ∑ i, gweight u h σ p i ≤ 1 + √(2 / π) := by sorry
