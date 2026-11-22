-- Prove2me | Theorems.Thm_Auto_cyclic_trace_control
-- name    : Auto.cyclic_trace_control
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:44:37.212038+00:00
-- url     : https://prove2.me/theorems/973d166d-c30e-4fe6-b7a6-de9da4755f39
-- title:
--   Auto: cyclic trace control
-- statement:
--   The Auto construction uses the cyclic trace control property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2854-L2915
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2854-L2915

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

theorem Auto.cyclic_trace_control (hD0 : D0.IsHermitian) (hD1 : D1.IsHermitian)
    (hD2 : D2.IsHermitian) {d : ℝ} (hd : 0 ≤ d)
    (h0 : ((d ^ 2 : ℝ) • (1 : Matrix ι ι ℂ) - D0 * D0).PosSemidef)
    (h1 : ((d ^ 2 : ℝ) • (1 : Matrix ι ι ℂ) - D1 * D1).PosSemidef)
    (h2 : ((d ^ 2 : ℝ) • (1 : Matrix ι ι ℂ) - D2 * D2).PosSemidef) :
    ENNReal.ofReal ‖(D0 * W0 * D1 * W1 * D2 * W2).trace‖ ≤ ENNReal.ofReal (5 / 3 * d) * (matCost
      ((rowMat W0 W2)ᴴ * rowMat W0 W2) ((rowMat W0 W2)ᴴ * D0 * rowMat W0 W2) + matCost ((rowMat W1
      W0)ᴴ * rowMat W1 W0) ((rowMat W1 W0)ᴴ * D1 * rowMat W1 W0) + matCost ((rowMat W2 W1)ᴴ *
      rowMat W2 W1) ((rowMat W2 W1)ᴴ * D2 * rowMat W2 W1)) := by sorry
