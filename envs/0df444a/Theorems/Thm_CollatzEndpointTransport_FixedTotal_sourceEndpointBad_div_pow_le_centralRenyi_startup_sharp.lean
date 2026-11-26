-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_sourceEndpointBad_div_pow_le_centralRenyi_startup_sharp
-- name    : CollatzEndpointTransport.FixedTotal.sourceEndpointBad_div_pow_le_centralRenyi_startup_sharp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:24:33.075188+00:00
-- url     : https://prove2.me/theorems/e54534a0-fb0c-4168-a85d-950a99240eb3
-- title:
--   Fixed Total: source Endpoint Bad div pow le central Renyi startup sharp
-- statement:
--   The Fixed Total construction uses the source Endpoint Bad div pow le central Renyi startup sharp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/SharpCentralRenyiPullback.lean#L1073-L1099
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/SharpCentralRenyiPullback.lean#L1073-L1099

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Definitions.Def_CollatzEndpointTransport_Linear_SharpCentralRenyiPullback
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.sourceEndpointBad_div_pow_le_centralRenyi_startup_sharp
    {S : Set ℕ} {C D theta eta : ℝ}
    (hS : QuantitativeDensity.IsCDDense S C D)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2)
    (M : ℕ) (hM : centralRenyiStartupScale theta eta ≤ M) :
    ((sourceEndpointBad S M).card : ℝ) / (2 ^ M : ℝ) ≤
      ((((M + 1) *
          2 ^ (M - centralRenyiDiscardDepth eta M) : ℕ) : ℝ) /
          (2 ^ M : ℝ)) +
        2 * Real.exp (-2 * (eta / 4) ^ 2 * M) +
        (C * Real.exp (-D * Real.log 3) +
            2 * (3 : ℝ) ^ theta * centralMomentConstant theta eta *
              (M + 1 : ℝ) ^ (1 + theta)) *
          Real.exp (-centralRenyiRate theta D * M) := by sorry
