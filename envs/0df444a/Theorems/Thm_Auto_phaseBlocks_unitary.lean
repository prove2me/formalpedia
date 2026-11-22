-- Prove2me | Theorems.Thm_Auto_phaseBlocks_unitary
-- name    : Auto.phaseBlocks_unitary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:44:19.556964+00:00
-- url     : https://prove2.me/theorems/aa52cf48-1fa5-46aa-9284-79f87f44d3bf
-- title:
--   Auto: phase Blocks unitary
-- statement:
--   The Auto construction uses the phase Blocks unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2843-L2852
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2843-L2852

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
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (W0 W1 W2 D0 D1 D2 : Matrix ι ι ℂ)

theorem Auto.phaseBlocks_unitary {c : ℂ} (hc : ‖c‖ = 1) (left : Bool) :
    (if left then Matrix.fromBlocks (c • (1 : Matrix ι ι ℂ)) 0 0 1 else Matrix.fromBlocks 1 0 0
      (c • (1 : Matrix ι ι ℂ))) * (if left then Matrix.fromBlocks (c • (1 : Matrix ι ι ℂ)) 0 0 1
      else Matrix.fromBlocks 1 0 0 (c • (1 : Matrix ι ι ℂ)))ᴴ = 1 := by sorry
