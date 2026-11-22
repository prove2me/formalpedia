-- Prove2me | Theorems.Thm_Auto_matCost_add3_le
-- name    : Auto.matCost_add3_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:42:30.401457+00:00
-- url     : https://prove2.me/theorems/6988eb78-a003-422a-9490-094e92db0424
-- title:
--   Auto: mat Cost add3 le
-- statement:
--   The Auto construction uses the mat Cost add3 le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1913-L1945
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1913-L1945

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
attribute [local instance] Auto._p2m_local_instance_5846efa9ac_1611
attribute [local instance] Auto._p2m_local_instance_5846efa9ac_1612
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem Auto.matCost_add3_le (P K₁ K₂ K₃ : Matrix n n ℂ) :
    matCost P (K₁ + K₂ + K₃) ≤ 3 * (matCost P K₁ + matCost P K₂ + matCost P K₃) := by sorry
