-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedReverseNonterminalSum_div_card_le
-- name    : CollatzEndpointTransport.FixedTotal.fixedReverseNonterminalSum_div_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:37:08.418637+00:00
-- url     : https://prove2.me/theorems/9bac9ea3-b04d-4f87-a952-d023492a8e4f
-- title:
--   Fixed Total: fixed Reverse Nonterminal Sum div card le
-- statement:
--   The complete nonterminal reverse-spend average is bounded by a
--   geometric series.  Including the harmless `r = 0` term keeps the formal
--   constant simple.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L823-L871
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L823-L871

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real NNReal
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.fixedReverseNonterminalSum_div_card_le
    {N s : ℕ} {theta : ℝ}
    (htheta : 0 < theta)
    (hN : 1 < N) (hs1 : 1 < s) (hsN : s < N)
    (hpiAlpha :
      centralSeparatorProportion N s < centralRenyiAlpha theta) :
    fixedReverseNonterminalSum N s theta /
        ((fixedSet N s).card : ℝ) ≤
      (N : ℝ) * (3 : ℝ) ^ (-theta) /
        (1 - centralRenyiRatio theta
          (centralSeparatorProportion N s)) := by sorry
