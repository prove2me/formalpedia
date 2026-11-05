-- Prove2me | solution 1 for levy_foundations_localLog_isOpen_goodDomain
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:17:41.436842+00:00
-- url     : https://prove2.me/submissions/43d679b6-d8f2-4107-89ef-d508f47653c7

import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Definitions.Def_levy_foundations_localLogGoodDomain
import Definitions.Def_levy_foundations_localLogExponent

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology

/-! Pull back the open slit plane under the continuous characteristic function. -/
theorem solution
    {E : Type*} [TopologicalSpace E] [Zero E]
    {φ : E → ℂ} (hφ_cont : Continuous φ) :
    IsOpen (LevyFoundations.LocalLog.goodDomain φ) := by
  exact Complex.isOpen_slitPlane.preimage hφ_cont
