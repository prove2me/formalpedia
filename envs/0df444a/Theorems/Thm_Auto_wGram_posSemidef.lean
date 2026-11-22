-- Prove2me | Theorems.Thm_Auto_wGram_posSemidef
-- name    : Auto.wGram_posSemidef
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:24:29.063745+00:00
-- url     : https://prove2.me/theorems/41c654e9-9196-4bb3-9260-f69d8094d7dd
-- title:
--   Auto: w Gram pos Semidef
-- statement:
--   The Auto construction uses the w Gram pos Semidef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2951-L2953
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2951-L2953

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
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
omit [DecidableEq κ] [Fintype κ]

theorem Auto.wGram_posSemidef [Finite κ] (B : Matrix ι κ ℂ) {f : ι → ℝ} (hf : ∀ i, 0 ≤ f i) :
    (wGram B f).PosSemidef := by sorry
