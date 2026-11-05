-- Prove2me | solution 1 for levy_foundations_localLog_exists_ball_subset_goodDomain
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T11:10:02.412108+00:00
-- url     : https://prove2.me/submissions/0b3745e0-4f61-436b-8fb9-60d37dd97643

import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Definitions.Def_levy_foundations_localLogGoodDomain
import Definitions.Def_levy_foundations_localLogExponent

open Filter Topology

theorem solution
    {E : Type*} [SeminormedAddCommGroup E]
    {φ : E → ℂ} (hφ_cont : Continuous φ) (hφ_zero : φ 0 = 1) :
    ∃ ε : ℝ, 0 < ε ∧ Metric.ball (0 : E) ε ⊆
      LevyFoundations.LocalLog.goodDomain φ := by
  have hopen : IsOpen (LevyFoundations.LocalLog.goodDomain φ) :=
    Complex.isOpen_slitPlane.preimage hφ_cont
  have h0 : (0 : E) ∈ LevyFoundations.LocalLog.goodDomain φ := by
    show φ 0 ∈ Complex.slitPlane
    rw [hφ_zero]; exact Complex.one_mem_slitPlane
  obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp hopen 0 h0
  exact ⟨ε, hε, hsub⟩
