-- Prove2me | Theorems.Thm_Auto_good_integrable
-- name    : Auto.good_integrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:23:28.603893+00:00
-- url     : https://prove2.me/theorems/3e5fce07-9da4-4dc7-933f-c2ca7129d3ec
-- title:
--   Auto: good integrable
-- statement:
--   The Auto construction uses the good integrable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4887-L4929
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4887-L4929

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

theorem Auto.good_integrable {Q : ℝ × (Fin 3 → ℝ) → ℝ} {sa sb σb β : ℝ} (hsa : 0 < sa) (hσb : 0 < σb)
    (hβ : 0 < β) (v : Fin 3) (hc : ContinuousOn Q (Set.Ioi 0 ×ˢ Set.univ))
    (hb : ∃ C, ∀ s ∈ Set.Icc sa sb, ∀ p, |Q (s, p)| ≤ C * HeatData.phi σb v p ^ 2) (m : ℕ) :
    (∀ s ∈ Set.Icc sa sb, Integrable (fun p => Gm β m s p * Q (s, p))) ∧ Integrable (fun z : ℝ ×
      (Fin 3 → ℝ) => Gm β m z.1 z.2 * Q z) ((volume.restrict (Set.Ioc sa sb)).prod volume) := by sorry
