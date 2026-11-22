-- Prove2me | Theorems.Thm_Auto_sum_eq_tsum_of_injective
-- name    : Auto.sum_eq_tsum_of_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:54:58.26573+00:00
-- url     : https://prove2.me/theorems/9a3abfb0-70fc-4bf4-8b71-7d99cbbc117a
-- title:
--   Auto: sum eq tsum of injective
-- statement:
--   The Auto construction uses the sum eq tsum of injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7432-L7436
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7432-L7436

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
public section
open scoped ENNReal NNReal
open MeasureTheory Filter Topology Real
public section
open Auto
open MeasureTheory Filter Topology Matrix Real
open scoped ENNReal NNReal MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section

theorem Auto.sum_eq_tsum_of_injective {T E : Type*} [Fintype T] [NormedAddCommGroup E]
    {d : ℕ} (e : T → (Fin d → ℤ)) (he : Function.Injective e)
    (f : (Fin d → ℤ) → E) (hs : ∀ z, f z ≠ 0 → z ∈ Set.range e) :
    ∑ t, f (e t) = ∑' z, f z := by sorry
