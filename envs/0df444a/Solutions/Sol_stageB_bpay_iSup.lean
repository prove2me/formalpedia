-- Prove2me | solution 1 for stageB_bpay_iSup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T01:35:51.964476+00:00
-- url     : https://prove2.me/submissions/075b4cd8-7351-467d-9338-e6c87800b875

import Mathlib
import Theorems.Thm_stageB_ndd_iff_rat
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open AvramDividend.Classical
open scoped Classical NNReal ENNReal
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b h q : ℝ) (hb : 0 < b) (hh : 0 < h) (ω : Ω) :
    (⨆ r : stageB_Bars h, stageB_bpay X (r : ℝ) b q ω) =
      if twoSidedExitUpTime X b ω < ⊤ ∧ NoDrawdownBeforeUpcrossing X.X b h ω then
        ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X b ω).toReal))) else 0 := by
  by_cases htop : twoSidedExitUpTime X b ω = ⊤
  · simp [stageB_bpay, htop]
  · have hiff := stageB_ndd_iff_rat X b h hb hh ω htop
    have hUtop : twoSidedExitUpTime X b ω < ⊤ := lt_top_iff_ne_top.mpr htop
    by_cases hnd : NoDrawdownBeforeUpcrossing X.X b h ω
    · obtain ⟨r, hr⟩ := hiff.mp hnd
      apply le_antisymm
      · refine iSup_le fun s => ?_
        by_cases hs : twoSidedExitUpTime X b ω < barrierRuinTime X (s : ℝ) ω <;>
          simp [stageB_bpay, hs, hnd, hUtop]
      · refine le_iSup_of_le r ?_
        have hcond : twoSidedExitUpTime X b ω < barrierRuinTime X (r : ℝ) ω := by
          by_contra hc
          have hz : stageB_bpay X (r : ℝ) b 0 ω = 0 := by
            simp [stageB_bpay, hc]
          exact hr hz
        have hpay : stageB_bpay X (r : ℝ) b q ω =
            ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X b ω).toReal))) := by
          simp [stageB_bpay, hcond]
        rw [hpay]
        simp [hnd, hUtop]
    · have hnone : ∀ r : stageB_Bars h,
          ¬ twoSidedExitUpTime X b ω < barrierRuinTime X (r : ℝ) ω := by
        intro r hrU
        have hb0 : stageB_bpay X (r : ℝ) b 0 ω ≠ 0 := by
          simp [stageB_bpay, hrU]
        exact hnd (hiff.mpr ⟨r, hb0⟩)
      simp [stageB_bpay, hnone, htop, hnd]
