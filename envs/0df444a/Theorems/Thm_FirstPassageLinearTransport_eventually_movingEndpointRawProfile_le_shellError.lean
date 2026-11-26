-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_eventually_movingEndpointRawProfile_le_shellError
-- name    : FirstPassageLinearTransport.eventually_movingEndpointRawProfile_le_shellError
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:44:02.409843+00:00
-- url     : https://prove2.me/theorems/5fd460ea-3fa8-5f1e-a164-7fe61f4142e3
-- title:
--   First Passage Linear Transport: eventually moving Endpoint Raw Profile le shell Error
-- statement:
--   Scalar closure of the literal sharp moving profile.  The high-rank
--   terms are absorbed by the fixed negative power supplied by the parameter
--   package, while both low-rank terms are paid by the exact critical buffer.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingEndpointAsymptotics.lean#L239-L453
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingEndpointAsymptotics.lean#L239-L453

import Definitions.Def_FirstPassageLinearTransport_MovingEndpointParameters
import Definitions.Def_FirstPassageLinearTransport_MovingEndpointScalars
import Definitions.Def_FirstPassageLinearTransport_MovingSharpTail
import Definitions.Def_FirstPassageLinearTransport_ShrinkingTailAsymptotics
import Definitions.Def_FirstPassageLinearTransport_TimeSupportScalars
import Definitions.Def_FirstPassageLinearTransport_MovingEndpointAsymptotics
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.eventually_movingEndpointRawProfile_le_shellError
    {Amax c beta : ℝ}
    (P : MovingEndpointParameterPackage Amax c beta)
    {A : ℕ → ℝ} {C D : ℝ}
    (hC : 0 < C) (hD : 0 < D)
    (hbuffer : Tendsto (movingRankBuffer A) atTop atTop)
    (hUpper : ∀ᶠ M : ℕ in atTop, A M ≤ Amax) :
    ∀ᶠ M : ℕ in atTop,
      let L := movingTerminalRank A M
      let H := (movingTimeSupportConstant P.run P.Cswitch + 1) *
        Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2))
      let dHi := shrinkingHighDensityProfile P.run P.Cswitch M
      let b := firstPassageEndpointRate - D / (L : ℝ)
      dHi + H * (1 + 6 / (P.run.rStar : ℝ)) *
          ((M : ℝ) + 1) ^ 2 * dHi +
        H * (1 + 6 / (P.run.rStar : ℝ)) *
          exactSharpCriticalLowSeriesConstant
            (firstPassageEndpointRate / 2) (C / 2) *
          (((L + 1 : ℕ) : ℝ) *
              Real.exp (-(Real.log 2 * (L : ℝ))) +
            Real.sqrt L *
              Real.exp (-(b * ((L - 1 : ℕ) : ℝ)))) ≤
        movingEndpointProfileConstant P C D *
          ((2 : ℝ) ^ (-(movingRankBuffer A M)) +
            (((M : ℝ) + 2) ^ (-P.epsilon))) := by sorry
