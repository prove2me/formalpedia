-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_choose_two_sub_div_fixedSet_eq_separator
-- name    : CollatzEndpointTransport.FixedTotal.choose_two_sub_div_fixedSet_eq_separator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:40:07.155375+00:00
-- url     : https://prove2.me/theorems/e4af0034-e289-4b75-b90b-8664ca785623
-- title:
--   Fixed Total: choose two sub div fixed Set eq separator
-- statement:
--   Removing one forced separator leaves exactly the one-point separator
--   probability.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedSizeSeparatorReverse.lean#L115-L138
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedSizeSeparatorReverse.lean#L115-L138

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeSeparatorMoment
import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeSeparatorReverse
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.choose_two_sub_div_fixedSet_eq_separator
    {N s : ℕ} (hN : 2 < N) (hs1 : 1 < s) (hsN : s < N) :
    (((N - 2).choose (s - 2) : ℕ) : ℝ) /
        ((fixedSet N s).card : ℝ) =
      centralSeparatorProportion N s := by sorry
