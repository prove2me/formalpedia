-- Prove2me | Theorems.Thm_Auto_matIntegral_wGram
-- name    : Auto.matIntegral_wGram
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:53:16.999419+00:00
-- url     : https://prove2.me/theorems/b75d17b5-9df1-474b-b380-835c1d04729e
-- title:
--   Auto: mat Integral w Gram
-- statement:
--   The Auto construction uses the mat Integral w Gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6462-L6476
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6462-L6476

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
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
open Auto
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem Auto.matIntegral_wGram {κ : Type*} {ν : Measure ℝ} (B : Matrix ι κ ℂ) (f : ℝ → ι → ℝ)
    (hf : ∀ i, Integrable (fun d => f d i) ν) :
    (∀ a b, Integrable (fun d => wGram B (f d) a b) ν) ∧ matIntegral ν (fun d => wGram B (f d))
      = wGram B (fun i => ∫ d, f d i ∂ν) := by sorry
