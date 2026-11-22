-- Prove2me | Theorems.Thm_Auto_heatCost_interval_bound
-- name    : Auto.heatCost_interval_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:54:16.669799+00:00
-- url     : https://prove2.me/theorems/5cd1dcb9-24ee-4fe6-8ff5-a865ec1b90a0
-- title:
--   Auto: heat Cost interval bound
-- statement:
--   Source `energy`: integrating dissipation on one interval uses only the initial energy.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6997-L7054
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6997-L7054

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
open MeasureTheory Filter Topology Matrix
open scoped ENNReal NNReal MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section

theorem Auto.heatCost_interval_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Hd : HeatData ι) {kk : ι → ℤ} (hk : Function.Injective kk)
    (hu : ∀ i, Hd.u i = Hd.h * kk i) (hh : 0 < Hd.h)
    {α : Fin 3 → ℝ} (hα : ∀ v, α v = 1 ∨ α v = 11 / 10)
    (hsum : α 0 + α 1 + α 2 = 16 / 5) {a b : ℝ}
    (ha : Hd.h ^ 2 ≤ a) (hab : a ≤ b) :
    ∫⁻ z, heatCost Hd α z ∂((volume.restrict (Set.Ioc a b)).prod volume) ≤
      ENNReal.ofReal (28 * (2 * Real.sqrt 2 * (1 + Real.sqrt (2 / Real.pi))) *
        ∑ v, Hd.nCube v) := by sorry
