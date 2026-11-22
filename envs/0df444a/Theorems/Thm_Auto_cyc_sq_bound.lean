-- Prove2me | Theorems.Thm_Auto_cyc_sq_bound
-- name    : Auto.cyc_sq_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:43:56.360098+00:00
-- url     : https://prove2.me/theorems/17b56b9d-9591-4acc-a19b-5a2953041af7
-- title:
--   Auto: cyc sq bound
-- statement:
--   The Auto construction uses the cyc sq bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2568-L2586
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2568-L2586

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

theorem Auto.cyc_sq_bound {d : ℝ} (h0 : ((d ^ 2 : ℝ) • (1 : Matrix ι ι ℂ) - D0 * D0).PosSemidef)
    (h1 : ((d ^ 2 : ℝ) • (1 : Matrix ι ι ℂ) - D1 * D1).PosSemidef)
    (h2 : ((d ^ 2 : ℝ) • (1 : Matrix ι ι ℂ) - D2 * D2).PosSemidef) :
    ((d ^ 2 : ℝ) • (1 : Matrix (Fin 3 × ι) (Fin 3 × ι) ℂ) - blk3 (cycDb D0 D1 D2) * blk3 (cycDb
      D0 D1 D2)).PosSemidef := by sorry
