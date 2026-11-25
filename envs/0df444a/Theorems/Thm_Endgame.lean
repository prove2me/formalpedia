-- Prove2me | Theorems.Thm_Endgame
-- name    : Endgame
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T15:55:50.889725+00:00
-- url     : https://prove2.me/theorems/14df854b-c4b2-4499-b611-01be51ab3ef6
-- title:
--   Endgame: Endgame
-- statement:
--   Paper, Section 3, the closing contradiction: under the constraints reached
--   there, `s + |b|/π - (2-δ)a + (1-a)^2/(2a)` is strictly negative.
--
--   Source: https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/Endgame.lean#L10-L22
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/Endgame.lean#L10-L22

module
public import Definitions.Def_PHarmonicPoly_CauchySchwarzPi
public import Definitions.Def_PHarmonicPoly_Endgame
public import Theorems.Thm_CauchySchwarzPi

set_option autoImplicit false
@[expose] public section
public section
open Real

theorem Endgame (a b s δ : ℝ)
    (_hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 13)
    (ha : 8 / 13 < a) (ha1 : a ≤ 1)
    (hs : 0 ≤ s) (hsq : s ^ 2 + b ^ 2 = 1) :
    s + |b| / Real.pi - (2 - δ) * a + (1 - a) ^ 2 / (2 * a) < 0 := by sorry
