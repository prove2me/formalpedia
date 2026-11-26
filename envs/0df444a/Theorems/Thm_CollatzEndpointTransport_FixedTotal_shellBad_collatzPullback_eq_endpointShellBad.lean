-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_shellBad_collatzPullback_eq_endpointShellBad
-- name    : CollatzEndpointTransport.FixedTotal.shellBad_collatzPullback_eq_endpointShellBad
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:57:28.605456+00:00
-- url     : https://prove2.me/theorems/a85cf870-fedb-473b-902e-c723a564ad67
-- title:
--   Fixed Total: shell Bad collatz Pullback eq endpoint Shell Bad
-- statement:
--   The Fixed Total construction uses the shell Bad collatz Pullback eq endpoint Shell Bad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalShellCoding.lean#L134-L157
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalShellCoding.lean#L134-L157

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalGlobalEndpointMoment
import Definitions.Def_CollatzEndpointTransport_Common_AffineCorrectionDensity
import Definitions.Def_CollatzEndpointTransport_Common_QuantitativePullbackDefs
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalShellCoding
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.shellBad_collatzPullback_eq_endpointShellBad
    (S : Set ℕ) (M : ℕ) :
    QuantitativeDensity.shellBad
        (QuantitativeDensity.collatzPullback S) M =
      endpointShellBad S M := by sorry
