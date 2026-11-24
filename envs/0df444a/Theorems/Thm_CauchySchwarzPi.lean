-- Prove2me | Theorems.Thm_CauchySchwarzPi
-- name    : CauchySchwarzPi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T14:58:38.251801+00:00
-- url     : https://prove2.me/theorems/f5d7bc4a-b493-4e58-a7cf-86b9ae8f0177
-- title:
--   Cauchy Schwarz Pi: Cauchy Schwarz Pi
-- statement:
--   Paper, Section 3: Cauchy-Schwarz together with `π > 3` gives
--   `s + |b|/π < 17/16` whenever `0 ≤ s` and `s^2 + b^2 = 1`.
--
--   Source: https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/CauchySchwarzPi.lean#L10-L26
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/CauchySchwarzPi.lean#L10-L26

module
public import Definitions.Def_PHarmonicPoly_Preamble
public import Definitions.Def_PHarmonicPoly_CauchySchwarzPi
set_option autoImplicit false
@[expose] public section
public section
open Real

theorem CauchySchwarzPi (b s : ℝ) (hs : 0 ≤ s) (hsq : s ^ 2 + b ^ 2 = 1) :
    s + |b| / Real.pi < 17 / 16 := by sorry
