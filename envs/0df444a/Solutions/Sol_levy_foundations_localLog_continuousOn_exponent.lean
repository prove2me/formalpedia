-- Prove2me | solution 1 for levy_foundations_localLog_continuousOn_exponent
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T11:10:04.038494+00:00
-- url     : https://prove2.me/submissions/671299f5-b6ad-4827-ba4a-1ef528df204c

import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Definitions.Def_levy_foundations_localLogGoodDomain
import Definitions.Def_levy_foundations_localLogExponent

open Filter Topology

theorem solution
    {E : Type*} [TopologicalSpace E] [Zero E]
    {φ : E → ℂ} (hφ_cont : Continuous φ) :
    ContinuousOn (LevyFoundations.LocalLog.localCharExponent φ)
      (LevyFoundations.LocalLog.goodDomain φ) := by
  exact hφ_cont.continuousOn.clog fun x hx => hx
