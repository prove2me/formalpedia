-- Prove2me | Theorems.Thm_Auto_hasDerivAt_wGram
-- name    : Auto.hasDerivAt_wGram
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:27:19.989267+00:00
-- url     : https://prove2.me/theorems/8ccc3543-86fa-40e6-8063-26f01cbc98ba
-- title:
--   Auto: has Deriv At w Gram
-- statement:
--   The Auto construction uses the has Deriv At w Gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2967-L2973
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2967-L2973

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

theorem Auto.hasDerivAt_wGram (B : Matrix ι κ ℂ) {f : ℝ → ι → ℝ} {f' : ι → ℝ} {θ₀ : ℝ}
    (hf : ∀ i, HasDerivAt (fun θ => f θ i) (f' i) θ₀) :
    ∀ a b, HasDerivAt (fun θ => wGram B (f θ) a b) (wGram B f' a b) θ₀ := by sorry
