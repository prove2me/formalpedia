-- Prove2me | Theorems.Thm_ChebNodeTelescope
-- name    : ChebNodeTelescope
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T15:13:36.732457+00:00
-- url     : https://prove2.me/theorems/d529f96f-ddda-4066-86be-323aaab95aa3
-- title:
--   Cheb Node Telescope: Cheb Node Telescope
-- statement:
--   The telescoping product that produces the paper's coefficient
--   `a_1 = 2/(1 - x_1)` at the first Chebyshev node.
--
--   Source: https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/ChebNodeTelescope.lean#L9-L104
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/ChebNodeTelescope.lean#L9-L104

module
public import Definitions.Def_PHarmonicPoly_Preamble
public import Definitions.Def_PHarmonicPoly_ChebNodeTelescope
set_option autoImplicit false
@[expose] public section
public section

theorem ChebNodeTelescope {m : ℕ} (hm : 2 ≤ m) :
    ∏ a ∈ Finset.Icc 2 m,
        (1 - Polynomial.Chebyshev.node m a) /
          (Polynomial.Chebyshev.node m 1 - Polynomial.Chebyshev.node m a) = 2 := by sorry
