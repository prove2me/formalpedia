-- Prove2me | solution 1 for levy_foundations_localLog_near_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:17:46.108289+00:00
-- url     : https://prove2.me/submissions/5bfac39f-d596-45f8-a8a2-ed9067462753

import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Definitions.Def_levy_foundations_localLogGoodDomain
import Definitions.Def_levy_foundations_localLogExponent

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology

/-! Continuity at the origin, transported from the original local-log lemma. -/
theorem solution
    {E : Type*} [SeminormedAddCommGroup E]
    {φ : E → ℂ} (hφ_cont : Continuous φ) (hφ_zero : φ 0 = 1) :
    Tendsto φ (𝓝 (0 : E)) (𝓝 (1 : ℂ)) := by
  rw [← hφ_zero]
  exact hφ_cont.continuousAt.tendsto
