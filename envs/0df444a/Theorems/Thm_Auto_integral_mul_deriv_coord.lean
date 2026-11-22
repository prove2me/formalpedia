-- Prove2me | Theorems.Thm_Auto_integral_mul_deriv_coord
-- name    : Auto.integral_mul_deriv_coord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:48:16.112918+00:00
-- url     : https://prove2.me/theorems/8c8520f8-3280-4536-adda-368e9b5bc8be
-- title:
--   Auto: integral mul deriv coord
-- statement:
--   The Auto construction uses the integral mul deriv coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4016-L4050
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4016-L4050

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

theorem Auto.integral_mul_deriv_coord {n : ℕ} (i : Fin (n + 1)) {F G F' G' : (Fin (n + 1) → ℝ) → ℝ}
    (hF : ∀ p, HasDerivAt (fun x => F (Function.update p i x)) (F' p) (p i))
    (hG : ∀ p, HasDerivAt (fun x => G (Function.update p i x)) (G' p) (p i))
    (h1 : Integrable (fun p => F p * G' p)) (h2 : Integrable (fun p => F' p * G p))
    (h3 : Integrable (fun p => F p * G p)) :
    ∫ p, F p * G' p = -∫ p, F' p * G p := by sorry
