-- Prove2me | Theorems.Thm_Auto_HeatData_family_good
-- name    : Auto.HeatData.family_good
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:23:44.781803+00:00
-- url     : https://prove2.me/theorems/eb0c24da-4614-44ac-8538-bee1d9984bc2
-- title:
--   Heat Data: family good
-- statement:
--   The Heat Data construction uses the family good property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L5005-L5052
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L5005-L5052

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
open Auto
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
open Auto.HeatData
variable (Hd : HeatData ι) (α : Fin 3 → ℝ) (η : ℝ) (v : Fin 3)

theorem Auto.HeatData.family_good (hh : 0 < Hd.h) (hη : 0 < η) (hα1 : ∀ k, 1 ≤ α k)
    (hα2 : ∀ k, α k ≤ 2) {sa sb : ℝ} (hsa : 0 < sa) (hab : sa ≤ sb) :
    ∀ Q ∈ ({Hd.qE α η v, Hd.qDr α η v, Hd.qDn α η v, Hd.qDp α η v,
      Hd.qV α η v + Hd.qA α η v, Hd.qYn α η v + Hd.qB α η v,
      Hd.qYp α η v + Hd.qC α η v, Hd.qZ α η v, Hd.qV α η v,
      Hd.qYn α η v, Hd.qYp α η v, Hd.qA α η v, Hd.qB α η v, Hd.qC α η v} :
        Set (ℝ → (Fin 3 → ℝ) → ℝ)),
      ContinuousOn (fun z : ℝ × (Fin 3 → ℝ) => Q z.1 z.2) (Set.Ioi 0 ×ˢ Set.univ) ∧
      ∃ C, ∀ s ∈ Set.Icc sa sb, ∀ p, |Q s p| ≤ C * phi (2 * sb) v p ^ 2 := by sorry
