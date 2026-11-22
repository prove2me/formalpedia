-- Prove2me | Theorems.Thm_Auto_matCost_eigen_sandwich
-- name    : Auto.matCost_eigen_sandwich
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:44:12.280117+00:00
-- url     : https://prove2.me/theorems/9d06c84e-e142-4a04-b830-2edc0ad0475b
-- title:
--   Auto: mat Cost eigen sandwich
-- statement:
--   The Auto construction uses the mat Cost eigen sandwich property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2623-L2664
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2623-L2664

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

theorem Auto.matCost_eigen_sandwich {κ : Type*} [Fintype κ] [DecidableEq κ]
    (U : Matrix.unitaryGroup κ ℂ) (m : κ → ℝ) (D : Matrix κ κ ℂ) :
    matCost (((U : Matrix κ κ ℂ) * diagonal (fun i => (m i : ℂ)) * star (U : Matrix κ κ ℂ)) *
      ((U : Matrix κ κ ℂ) * diagonal (fun i => (m i : ℂ)) * star (U : Matrix κ κ ℂ))) (((U :
      Matrix κ κ ℂ) * diagonal (fun i => (m i : ℂ)) * star (U : Matrix κ κ ℂ)) * D * ((U : Matrix
      κ κ ℂ) * diagonal (fun i => (m i : ℂ)) * star (U : Matrix κ κ ℂ))) = ENNReal.ofReal ((3 / 2)
      * ∑ i, ∑ j, |m i| ^ 2 * |m j| ^ 2 * ‖(star (U : Matrix κ κ ℂ) * D * U) i j‖ ^ 2 / (|m i| +
      |m j|)) := by sorry
