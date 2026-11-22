-- Prove2me | Theorems.Thm_Auto_gram_heat_identity
-- name    : Auto.gram_heat_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:27:27.084369+00:00
-- url     : https://prove2.me/theorems/5c139489-fca8-433c-a991-48aa20f37cbc
-- title:
--   Auto: gram heat identity
-- statement:
--   The Auto construction uses the gram heat identity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3012-L3060
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3012-L3060

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
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem Auto.gram_heat_identity (C : Matrix κ κ ℂ) (hC : C.PosSemidef) (B : Matrix ι κ ℂ) (u : ι → ℝ)
    {h η σ : ℝ} (hh : 0 ≤ h) (hη : 0 < η) (hσ : 0 < σ) (p : ℝ) :
    HasDerivAt (fun q => energyReg η (C + wGram B (gweight u h σ q))) ((3 / 2) * ((CFC.sqrt (C +
      wGram B (gweight u h σ p) + (η : ℂ) • 1) * wGram B (fun i => -(h * gaussianD 1 σ (u i -
      p)))).trace).re) p ∧ HasDerivAt (fun q => (3 / 2) * ((CFC.sqrt (C + wGram B (gweight u h σ
      q) + (η : ℂ) • 1) * wGram B (fun i => -(h * gaussianD 1 σ (u i - q)))).trace).re) ((matCost
      (C + wGram B (gweight u h σ p) + (η : ℂ) • 1) (wGram B (fun i => -(h * gaussianD 1 σ (u i -
      p))))).toReal + (3 / 2) * ((CFC.sqrt (C + wGram B (gweight u h σ p) + (η : ℂ) • 1) * wGram B
      (fun i => h * gaussianD 2 σ (u i - p))).trace).re) p ∧ HasDerivAt (fun τ => energyReg η (C +
      wGram B (gweight u h τ p))) ((3 / 2) * ((CFC.sqrt (C + wGram B (gweight u h σ p) + (η : ℂ) •
      1) * wGram B (fun i => h * gaussianD 2 σ (u i - p) / 2)).trace).re) σ := by sorry
