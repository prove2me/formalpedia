-- Prove2me | Theorems.Thm_Auto_ae_sub_of_ae
-- name    : Auto.ae_sub_of_ae
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T19:02:14.686562+00:00
-- url     : https://prove2.me/theorems/03549934-2e09-483d-9309-39683890e781
-- title:
--   Auto: ae sub of ae
-- statement:
--   The Auto construction uses the ae sub of ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L618-L620
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L618-L620

module
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Definitions.Def_Triangular_Auto_Carleson
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal Convolution
noncomputable section

theorem Auto.ae_sub_of_ae {P : ℝ → Prop} (h : ∀ᵐ x, P x) : ∀ᵐ p : ℝ × ℝ, P (p.1 - p.2) := by sorry
