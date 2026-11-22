-- Prove2me | Theorems.Thm_Auto_sq_smul_one_sub_rdiag_psd
-- name    : Auto.sq_smul_one_sub_rdiag_psd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:54:34.804053+00:00
-- url     : https://prove2.me/theorems/dec74811-2b03-4184-a2c2-b62204b8c024
-- title:
--   Auto: sq smul one sub rdiag psd
-- statement:
--   A bounded real diagonal matrix has the corresponding operator-norm bound.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7101-L7113
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7101-L7113

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

theorem Auto.sq_smul_one_sub_rdiag_psd {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : ι → ℝ} {d : ℝ} (hf : ∀ i, |f i| ≤ d) :
    ((d ^ 2 : ℝ) • (1 : Matrix ι ι ℂ) - rdiag f * rdiag f).PosSemidef := by sorry
