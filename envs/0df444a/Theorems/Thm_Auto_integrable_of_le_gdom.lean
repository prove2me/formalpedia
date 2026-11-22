-- Prove2me | Theorems.Thm_Auto_integrable_of_le_gdom
-- name    : Auto.integrable_of_le_gdom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:36:37.583083+00:00
-- url     : https://prove2.me/theorems/ec3b20dc-7dc7-432d-9ca9-76e42f36c03d
-- title:
--   Auto: integrable of le gdom
-- statement:
--   The Auto construction uses the integrable of le gdom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4826-L4829
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4826-L4829

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

theorem Auto.integrable_of_le_gdom {f : (Fin 3 → ℝ) → ℝ} (hf : Continuous f) {C ε : ℝ} (hε : 0 < ε)
    (hb : ∀ p, |f p| ≤ C * gdom ε p) :
    Integrable f := by sorry
