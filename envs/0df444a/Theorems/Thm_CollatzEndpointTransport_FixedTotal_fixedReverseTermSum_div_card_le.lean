-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedReverseTermSum_div_card_le
-- name    : CollatzEndpointTransport.FixedTotal.fixedReverseTermSum_div_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:36:58.318328+00:00
-- url     : https://prove2.me/theorems/4b125c4c-cef5-5104-a428-2e9051e104d3
-- title:
--   Fixed Total: fixed Reverse Term Sum div card le
-- statement:
--   One nonterminal reverse-spend term, averaged over a fixed composition
--   level, is bounded by the exact geometric ratio from the paper.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L690-L781
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L690-L781

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.fixedReverseTermSum_div_card_le
    {N s r : ℕ} {theta : ℝ}
    (htheta : 0 < theta)
    (hN : 1 < N) (hs1 : 1 < s) (hsN : s < N)
    (hr0 : 0 < r) (hrs : r < s) :
    fixedReverseTermSum N s theta r / ((fixedSet N s).card : ℝ) ≤
      (N : ℝ) * (3 : ℝ) ^ (-theta) *
        centralRenyiRatio theta (centralSeparatorProportion N s) ^ r := by sorry
