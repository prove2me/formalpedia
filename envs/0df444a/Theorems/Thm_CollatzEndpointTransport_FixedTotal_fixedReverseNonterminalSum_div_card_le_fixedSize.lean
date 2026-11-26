-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedReverseNonterminalSum_div_card_le_fixedSize
-- name    : CollatzEndpointTransport.FixedTotal.fixedReverseNonterminalSum_div_card_le_fixedSize
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:40:51.279963+00:00
-- url     : https://prove2.me/theorems/a3dd5f61-9ac7-4464-9313-233c33da225e
-- title:
--   Fixed Total: fixed Reverse Nonterminal Sum div card le fixed Size
-- statement:
--   The complete nonterminal reverse-spend average with no
--   population-size conditioning loss.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedSizeSeparatorReverse.lean#L297-L396
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedSizeSeparatorReverse.lean#L297-L396

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeSeparatorMoment
import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeSeparatorReverse
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.fixedReverseNonterminalSum_div_card_le_fixedSize
    {N s : ℕ} {theta : ℝ}
    (htheta : 0 < theta)
    (hN : 2 < N) (hs1 : 1 < s) (hsN : s < N)
    (hpiAlpha :
      centralSeparatorProportion N s < centralRenyiAlpha theta) :
    fixedReverseNonterminalSum N s theta /
        ((fixedSet N s).card : ℝ) ≤
      centralSeparatorProportion N s /
        ((2 : ℝ) ^ theta - 1 -
          centralSeparatorProportion N s * ((3 : ℝ) ^ theta - 1)) := by sorry
