-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_stageOrbit_le_power
-- name    : FirstPassageLinearTransport.stageOrbit_le_power
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:35:35.835884+00:00
-- url     : https://prove2.me/theorems/d4ef7791-17f6-4c68-a19e-06698d5cb64f
-- title:
--   First Passage Linear Transport: stage Orbit le power
-- statement:
--   Coarse all-stage contraction.  The factor `stageK^R` is deliberately
--   weaker than the paper's bounded geometric factor, but remains only
--   polynomial on the logarithmic stage schedule and is easier to audit.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Bootstrap.lean#L405-L452
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Bootstrap.lean#L405-L452

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_FirstPassageLinearTransport_Parameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_Bootstrap
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology BigOperators
noncomputable section

theorem FirstPassageLinearTransport.stageOrbit_le_power
    {r eta : ℝ} (p : StageSetup r eta) {R n : ℕ}
    (hn : 0 < n) (hnSet : n ∈ bootstrapSet p R) :
    (stageOrbit p R n : ℝ) ≤
      stageK p ^ R * (n : ℝ) ^ (r ^ R) := by sorry
