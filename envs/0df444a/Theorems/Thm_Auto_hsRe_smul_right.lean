-- Prove2me | Theorems.Thm_Auto_hsRe_smul_right
-- name    : Auto.hsRe_smul_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:26:21.745803+00:00
-- url     : https://prove2.me/theorems/1e41bf82-0a43-478e-9b23-c89afd5a10db
-- title:
--   Auto: hs Re smul right
-- statement:
--   The Auto construction uses the hs Re smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L617-L619
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L617-L619

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
variable {m n : Type*} [Fintype m] [Fintype n]

theorem Auto.hsRe_smul_right (c : ℝ) (X Y : Matrix m n ℂ) :
    hsRe X (c • Y) = c * hsRe X Y := by sorry
