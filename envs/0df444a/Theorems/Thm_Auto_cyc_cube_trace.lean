-- Prove2me | Theorems.Thm_Auto_cyc_cube_trace
-- name    : Auto.cyc_cube_trace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:43:33.461777+00:00
-- url     : https://prove2.me/theorems/dc2f675b-4768-4557-bca5-dcf651e9020a
-- title:
--   Auto: cyc cube trace
-- statement:
--   The Auto construction uses the cyc cube trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2515-L2541
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2515-L2541

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

theorem Auto.cyc_cube_trace :
    ((blk3 (cycDb D0 D1 D2) * blk3 (cycMb W0 W1 W2)) ^ 3).trace = 3 * (D0 * W0 * D1 * W1 * D2 *
      W2).trace + 3 * (D0 * W2ᴴ * D2 * W1ᴴ * D1 * W0ᴴ).trace := by sorry
