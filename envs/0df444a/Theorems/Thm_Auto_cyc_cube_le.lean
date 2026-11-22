-- Prove2me | Theorems.Thm_Auto_cyc_cube_le
-- name    : Auto.cyc_cube_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T18:44:23.356953+00:00
-- url     : https://prove2.me/theorems/0c674cf3-4e40-4b12-b631-777d85eb2405
-- title:
--   Auto: cyc cube le
-- statement:
--   The Auto construction uses the cyc cube le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2666-L2829
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2666-L2829

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

theorem Auto.cyc_cube_le (hD0 : D0.IsHermitian) (hD1 : D1.IsHermitian) (hD2 : D2.IsHermitian) {d : ℝ}
    (hd : 0 ≤ d) (h0 : ((d ^ 2 : ℝ) • (1 : Matrix ι ι ℂ) - D0 * D0).PosSemidef)
    (h1 : ((d ^ 2 : ℝ) • (1 : Matrix ι ι ℂ) - D1 * D1).PosSemidef)
    (h2 : ((d ^ 2 : ℝ) • (1 : Matrix ι ι ℂ) - D2 * D2).PosSemidef) :
    ENNReal.ofReal ‖((blk3 (cycDb D0 D1 D2) * blk3 (cycMb W0 W1 W2)) ^ 3).trace‖ ≤
      ENNReal.ofReal (10 * d) * (matCost ((rowMat W0 W2)ᴴ * rowMat W0 W2) ((rowMat W0 W2)ᴴ * D0 *
      rowMat W0 W2) + matCost ((rowMat W1 W0)ᴴ * rowMat W1 W0) ((rowMat W1 W0)ᴴ * D1 * rowMat W1
      W0) + matCost ((rowMat W2 W1)ᴴ * rowMat W2 W1) ((rowMat W2 W1)ᴴ * D2 * rowMat W2 W1)) := by sorry
