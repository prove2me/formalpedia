-- Prove2me | Theorems.Thm_AbsorbK
-- name    : AbsorbK
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T14:58:47.11983+00:00
-- url     : https://prove2.me/theorems/bcedb426-7095-4732-94f2-dcf084d3b691
-- title:
--   Absorb K: Absorb K
-- statement:
--   Paper, Section 3: the `k = n-2` absorption step, with `p-1 = k+1-δ` and
--   `p-2 = k-δ` already substituted.
--
--   Source: https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/AbsorbK.lean#L10-L14
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/AbsorbK.lean#L10-L14

module
public import Definitions.Def_PHarmonicPoly_Preamble
public import Definitions.Def_PHarmonicPoly_AbsorbK
set_option autoImplicit false
@[expose] public section
public section
open Real

theorem AbsorbK (k δ a b s A : ℝ) (hk : 1 ≤ k) (hδ0 : 0 ≤ δ) (hA : 0 ≤ A)
    (hsa : (1 - δ) * a ≤ s) :
    s - (k + 1 - δ) * a + k * (|b| / Real.pi) + (k - δ) * A
      ≤ k * (s + |b| / Real.pi - (2 - δ) * a + A) := by sorry
