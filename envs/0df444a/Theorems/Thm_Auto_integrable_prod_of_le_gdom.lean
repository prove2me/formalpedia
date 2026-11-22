-- Prove2me | Theorems.Thm_Auto_integrable_prod_of_le_gdom
-- name    : Auto.integrable_prod_of_le_gdom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:50:52.364357+00:00
-- url     : https://prove2.me/theorems/7a7c7726-a9d1-4d57-89b4-9e9889d3bb4e
-- title:
--   Auto: integrable prod of le gdom
-- statement:
--   The Auto construction uses the integrable prod of le gdom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4831-L4850
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4831-L4850

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

theorem Auto.integrable_prod_of_le_gdom {f : ℝ × (Fin 3 → ℝ) → ℝ} {sa sb : ℝ} (hsa : 0 < sa)
    (hf : ContinuousOn f (Set.Ioi 0 ×ˢ Set.univ)) {C ε : ℝ} (hε : 0 < ε)
    (hb : ∀ s ∈ Set.Ioc sa sb, ∀ p, |f (s, p)| ≤ C * gdom ε p) :
    Integrable f ((volume.restrict (Set.Ioc sa sb)).prod volume) := by sorry
