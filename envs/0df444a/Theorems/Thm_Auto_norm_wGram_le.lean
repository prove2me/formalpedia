-- Prove2me | Theorems.Thm_Auto_norm_wGram_le
-- name    : Auto.norm_wGram_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:48:37.32781+00:00
-- url     : https://prove2.me/theorems/e0c2fe58-46b3-4b0f-9264-a551721af78b
-- title:
--   Auto: norm w Gram le
-- statement:
--   The Auto construction uses the norm w Gram le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4119-L4133
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4119-L4133

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
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem Auto.norm_wGram_le {κ : Type*} (B : Matrix ι κ ℂ) (f : ι → ℝ) {β γ : ℝ}
    (hB : ∀ i a, ‖B i a‖ ≤ β) (hf : ∀ i, |f i| ≤ γ) (a b : κ) :
    ‖wGram B f a b‖ ≤ Fintype.card ι * (β * γ * β) := by sorry
