-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_eventually_movingTerminalRank_lt_shrinkingSwitchRank
-- name    : FirstPassageLinearTransport.eventually_movingTerminalRank_lt_shrinkingSwitchRank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:17:18.490543+00:00
-- url     : https://prove2.me/theorems/27567720-db97-57ff-bdbf-e11bdc06fcf8
-- title:
--   First Passage Linear Transport: eventually moving Terminal Rank lt shrinking Switch Rank
-- statement:
--   A pointwise upper bound on the moving exponent places its terminal rank
--   below the fixed logarithmic switch selected by the parameter package.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingEndpointScalars.lean#L383-L398
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingEndpointScalars.lean#L383-L398

import Definitions.Def_FirstPassageLinearTransport_ShrinkingParameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_MovingEndpointScalars
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.eventually_movingTerminalRank_lt_shrinkingSwitchRank
    {A : ℕ → ℝ} {Amax C : ℝ}
    (hAmax : 0 ≤ Amax) (hAC : Amax / Real.log 2 < C)
    (hUpper : ∀ᶠ M : ℕ in atTop, A M ≤ Amax) :
    ∀ᶠ M : ℕ in atTop,
      movingTerminalRank A M < shrinkingSwitchRank C M := by sorry
