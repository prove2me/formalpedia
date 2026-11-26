-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedReverseMajorantAverage_le
-- name    : CollatzEndpointTransport.FixedTotal.fixedReverseMajorantAverage_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:37:19.095238+00:00
-- url     : https://prove2.me/theorems/77946cfe-aaf6-4d86-a1d0-281aec24cefa
-- title:
--   Fixed Total: fixed Reverse Majorant Average le
-- statement:
--   Central reverse-spend moment bound before making its constant uniform
--   over a prescribed central window.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L949-L996
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L949-L996

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

theorem CollatzEndpointTransport.FixedTotal.fixedReverseMajorantAverage_le
    {N s : ℕ} {theta : ℝ}
    (htheta0 : 0 < theta)
    (hN : 1 < N) (hs1 : 1 < s) (hsN : s < N)
    (hpiAlpha :
      centralSeparatorProportion N s < centralRenyiAlpha theta)
    (hcontract : 3 ^ s ≤ 2 ^ N) :
    fixedReverseMajorantAverage N s theta ≤
      (N : ℝ) * (3 : ℝ) ^ (-theta) /
        (1 - centralRenyiRatio theta
          (centralSeparatorProportion N s)) + 2 := by sorry
