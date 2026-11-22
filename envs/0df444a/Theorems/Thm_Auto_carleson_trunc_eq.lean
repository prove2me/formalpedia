-- Prove2me | Theorems.Thm_Auto_carleson_trunc_eq
-- name    : Auto.carleson_trunc_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T19:01:18.238168+00:00
-- url     : https://prove2.me/theorems/2d3cb92b-d706-4a0a-8888-2de97a08f62b
-- title:
--   Auto: carleson trunc eq
-- statement:
--   Integrating out `u` turns the truncation into a modulated kernel in `(x, t)`.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L319-L340
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L319-L340

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

theorem Auto.carleson_trunc_eq (a ν : ℝ → ℝ) (g : ℝ → ℂ) (σ ε : ℝ)
    (hint : Integrable (carlesonTrunc a ν g σ ε)) :
    Integrable (fun p : ℝ × ℝ => carlesonH a ν g σ ε p * (carlesonWeight p.2 : ℂ)) ∧
      ∫ q, carlesonTrunc a ν g σ ε q =
        ∫ p : ℝ × ℝ, carlesonH a ν g σ ε p * (carlesonWeight p.2 : ℂ) := by sorry
