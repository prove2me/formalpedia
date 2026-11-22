-- Prove2me | Theorems.Thm_Auto_plane_integral_prod01
-- name    : Auto.plane_integral_prod01
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:51:45.743109+00:00
-- url     : https://prove2.me/theorems/ed9fd9f4-a991-4c31-b324-7a8e8a7d4fe2
-- title:
--   Auto: plane integral prod01
-- statement:
--   The Auto construction uses the plane integral prod01 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L5541-L5591
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L5541-L5591

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

theorem Auto.plane_integral_prod01 {k f g : ℝ → ℝ} (hk : Continuous k) (hf : Continuous f)
    (hg : Continuous g) (hki : Integrable k) (hfi : Integrable f) (hgi : Integrable g) :
    Integrable (fun p : Fin 3 → ℝ => k (p 0 + p 1 + p 2) * (f (p 0) * g (p 1))) ∧ ∫ p : Fin 3 →
      ℝ, k (p 0 + p 1 + p 2) * (f (p 0) * g (p 1)) = (∫ t, k t) * ((∫ t, f t) * (∫ t, g t)) := by sorry
