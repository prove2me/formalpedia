-- Prove2me | Theorems.Thm_Auto_eLpNorm_toReal_le_of_strip
-- name    : Auto.eLpNorm_toReal_le_of_strip
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T19:01:47.829039+00:00
-- url     : https://prove2.me/theorems/71fa82e9-af55-45ca-8225-0c6164ae919e
-- title:
--   Auto: e Lp Norm to Real le of strip
-- statement:
--   An L³ bound for planar functions dominated by `|a(x)|` on a strip `|y + c x| ≤ r`.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L479-L531
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L479-L531

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

theorem Auto.eLpNorm_toReal_le_of_strip {f : ℝ × ℝ → ℂ} {a : ℝ → ℝ} {r c : ℝ} (hr : 0 ≤ r)
    (ha : Measurable a) (ha₃ : Integrable fun x => |a x| ^ 3)
    (hf : ∀ p, ‖f p‖ ≤ |a p.1|) (hz : ∀ p, r < |p.2 + c * p.1| → f p = 0) :
    (eLpNorm f 3 volume).toReal ≤ (2 * r * ∫ x, |a x| ^ 3) ^ (1 / 3 : ℝ) := by sorry
