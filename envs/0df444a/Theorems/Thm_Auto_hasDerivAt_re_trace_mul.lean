-- Prove2me | Theorems.Thm_Auto_hasDerivAt_re_trace_mul
-- name    : Auto.hasDerivAt_re_trace_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:30:38.346581+00:00
-- url     : https://prove2.me/theorems/9ec6c531-69cb-4a8a-864d-f68581cceb89
-- title:
--   Auto: has Deriv At re trace mul
-- statement:
--   The Auto construction uses the has Deriv At re trace mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1332-L1341
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1332-L1341

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
open Auto
noncomputable section
variable {n : Type*} [Fintype n] [DecidableEq n]
omit [DecidableEq n]

theorem Auto.hasDerivAt_re_trace_mul {F G : ℝ → Matrix n n ℂ} {F' G' : Matrix n n ℂ} {θ₀ : ℝ}
    (hF : ∀ i j, HasDerivAt (fun θ => F θ i j) (F' i j) θ₀)
    (hG : ∀ i j, HasDerivAt (fun θ => G θ i j) (G' i j) θ₀) :
    HasDerivAt (fun θ => ((F θ * G θ).trace).re) (((F' * G θ₀ + F θ₀ * G').trace).re) θ₀ := by sorry
