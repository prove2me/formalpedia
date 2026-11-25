-- Prove2me | Theorems.Thm_DeficitPoly
-- name    : DeficitPoly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:40:31.521217+00:00
-- url     : https://prove2.me/theorems/800b35f8-4c48-4845-b5fa-9615fee3a402
-- title:
--   Deficit Poly: Deficit Poly
-- statement:
--   The algebraic form of the deficit estimate: for `P` of degree at most `m`,
--   bounded by `1` on `[-1,1]` and normalised by `P 1 = 1`, the deficit
--   `m^2 - P'(1)` dominates `2(1 + P x_1)/(1 - x_1)`.
--
--   Source: https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/DeficitPoly.lean#L11-L104
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/DeficitPoly.lean#L11-L104

module
public import Definitions.Def_PHarmonicPoly_LagrangeDerivCoeffOne
public import Definitions.Def_PHarmonicPoly_LagrangeDerivSigns
public import Definitions.Def_PHarmonicPoly_DeficitPoly
public import Theorems.Thm_LagrangeDerivCoeffOne
public import Theorems.Thm_LagrangeDerivSigns

set_option autoImplicit false
@[expose] public section
public section

theorem DeficitPoly {m : ℕ} (hm : 2 ≤ m) {P : Polynomial ℝ}
    (hdeg : P.degree ≤ (m : ℕ))
    (hbd : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |P.eval x| ≤ 1) (h1 : P.eval 1 = 1) :
    2 * (1 + P.eval (Polynomial.Chebyshev.node m 1))
      ≤ ((m : ℝ) ^ 2 - (Polynomial.derivative P).eval 1)
          * (1 - Polynomial.Chebyshev.node m 1) := by sorry
