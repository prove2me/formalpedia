-- Prove2me | Theorems.Thm_Auto_carleson_integrand_coord
-- name    : Auto.carleson_integrand_coord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T19:01:14.308381+00:00
-- url     : https://prove2.me/theorems/5479a27a-a575-4bea-be28-7e57f6eabb68
-- title:
--   Auto: carleson integrand coord
-- statement:
--   The Auto construction uses the carleson integrand coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L283-L310
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L283-L310

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

theorem Auto.carleson_integrand_coord (a ν : ℝ → ℝ) (g : ℝ → ℂ) (σ ε : ℝ) (q : (ℝ × ℝ) × ℝ) :
    (let r := carlesonCoord q
     if ε < |r.1.1 + r.1.2 + r.2| then
       carlesonF₀ a ν σ r.1 * carlesonF₁ g (r.1.2, r.2) * carlesonF₂ a ν σ (r.2, r.1.1) /
         ((r.1.1 + r.1.2 + r.2 : ℝ) : ℂ) else 0) =
      carlesonH a ν g σ ε q.1 * (carlesonW q.1.2 q.2 : ℂ) := by sorry
