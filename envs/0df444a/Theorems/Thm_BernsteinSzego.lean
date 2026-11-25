-- Prove2me | Theorems.Thm_BernsteinSzego
-- name    : BernsteinSzego
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:44:45.523929+00:00
-- url     : https://prove2.me/theorems/1369259e-c587-433c-8648-e73788a800f8
-- title:
--   Bernstein Szego: Bernstein Szego
-- statement:
--   The Bernstein-Szego inequality: a real trigonometric polynomial `T` of
--   degree at most `m ≥ 1` with `‖T‖_∞ ≤ 1` satisfies `T^2 + (T')^2/m^2 ≤ 1`.
--
--   Source: https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/BernsteinSzego.lean#L13-L242
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/BernsteinSzego.lean#L13-L242

module
public import Definitions.Def_PHarmonicPoly_TrigPolyZeroCount
public import Definitions.Def_PHarmonicPoly_TrigPolyLinComb
public import Definitions.Def_PHarmonicPoly_TrigPolySmooth
public import Definitions.Def_PHarmonicPoly_InteriorZeroOfSignChange
public import Definitions.Def_PHarmonicPoly_AngleOfUnitCirclePoint
public import Definitions.Def_PHarmonicPoly_BernsteinSzego
public import Theorems.Thm_AngleOfUnitCirclePoint
public import Theorems.Thm_InteriorZeroOfSignChange
public import Theorems.Thm_TrigPolyLinComb
public import Theorems.Thm_TrigPolySmooth
public import Theorems.Thm_TrigPolyZeroCount

set_option autoImplicit false
@[expose] public section
public section

theorem BernsteinSzego {m : ℕ} (hm : 1 ≤ m) {T : ℝ → ℝ} (hT : TrigPolyLe m T)
    (hbd : ∀ t : ℝ, |T t| ≤ 1) :
    ∀ t : ℝ, (T t) ^ 2 + (deriv T t) ^ 2 / (m : ℝ) ^ 2 ≤ 1 := by sorry
