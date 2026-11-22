-- Prove2me | Theorems.Thm_Auto_HeatData_gram_scalar_bounds
-- name    : Auto.HeatData.gram_scalar_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:49:53.161728+00:00
-- url     : https://prove2.me/theorems/d003aed2-40cc-446c-ac49-d458ece204d2
-- title:
--   Heat Data: gram scalar bounds
-- statement:
--   The Heat Data construction uses the gram scalar bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4448-L4489
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4448-L4489

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
variable (Hd : HeatData ι)

theorem Auto.HeatData.gram_scalar_bounds {κ : Type*} [Fintype κ] [DecidableEq κ] {N C₀ φ η : ℝ}
    (hN : (Fintype.card κ : ℝ) ≤ N) (hC₀ : 0 ≤ C₀) (hφ : 0 ≤ φ) (hφ2 : φ ≤ 2) (hη : 0 < η)
    {Γ : Matrix κ κ ℂ} (hΓ : Γ.PosSemidef) (hΓb : ∀ a b, ‖Γ a b‖ ≤ C₀ * φ ^ 2) :
    (∀ K : Matrix κ κ ℂ, (∀ a b, ‖K a b‖ ≤ C₀ * φ ^ 2) → |tr32 η Γ K| ≤ (3 / 2) * √(N * (4 * C₀)
      + N * η) * N * C₀ * φ ^ 2 ∧ |(matCost (Γ + (η : ℂ) • 1) K).toReal| ≤ (3 / 4) * N ^ 2 * (4 *
      C₀) * C₀ / √η * φ ^ 2) ∧ |energyReg η Γ| ≤ 2 * N * C₀ * √(N * (4 * C₀) + η) * φ ^ 2 := by sorry
