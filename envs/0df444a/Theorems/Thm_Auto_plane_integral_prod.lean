-- Prove2me | Theorems.Thm_Auto_plane_integral_prod
-- name    : Auto.plane_integral_prod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:51:50.650817+00:00
-- url     : https://prove2.me/theorems/dbf4db14-a461-4209-947a-759d15e2dec3
-- title:
--   Auto: plane integral prod
-- statement:
--   The Auto construction uses the plane integral prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L5593-L5622
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L5593-L5622

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

theorem Auto.plane_integral_prod {k f g : ℝ → ℝ} (hk : Continuous k) (hf : Continuous f)
    (hg : Continuous g) (hki : Integrable k) (hfi : Integrable f) (hgi : Integrable g)
    {a b : Fin 3} (hab : a ≠ b) :
    Integrable (fun p : Fin 3 → ℝ => k (p 0 + p 1 + p 2) * (f (p a) * g (p b))) ∧ ∫ p : Fin 3 →
      ℝ, k (p 0 + p 1 + p 2) * (f (p a) * g (p b)) = (∫ t, k t) * ((∫ t, f t) * (∫ t, g t)) := by sorry
