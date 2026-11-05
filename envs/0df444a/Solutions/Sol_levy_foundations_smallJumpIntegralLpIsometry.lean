-- Prove2me | solution 1 for levy_foundations_smallJumpIntegralLpIsometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T00:52:25.563214+00:00
-- url     : https://prove2.me/submissions/153483c8-7c67-4245-a707-18cc2c64e9f6

import Mathlib.MeasureTheory.Function.L2Space
import Definitions.Def_levy_foundations_smallJumpIntegralLp
import Definitions.Def_levy_foundations_isCompensatedPoissonL2Extension
import Theorems.Thm_levy_foundations_smallJumpBandMemLpTwo
import Theorems.Thm_ProbabilityTheory_eLpNorm_sq_bandFun

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (ν : Measure ℝ)
    [SigmaFinite ν] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (K : ℕ → Ω → ℕ)
    (X : ℕ → ℕ → Ω → ℝ × ℝ)
    (I : Lp ℝ 2 (volume.prod ν) → Lp ℝ 2 μ)
    (hI : LevyFoundations.IsCompensatedPoissonL2Extension
      (volume.prod ν) μ K X I)
    (hν : LevyFoundations.isLevyMeasure ν) (t : ℝ) (ht : 0 ≤ t) :
    (eLpNorm (LevyFoundations.smallJumpIntegralLp ν μ I hν t) 2 μ) ^ 2 =
      ENNReal.ofReal t * ∫⁻ x in Set.Ioo (-1) 1,
        ENNReal.ofReal (x ^ 2) ∂ν := by
  classical
  let f : ℝ × ℝ → ℝ :=
    (Set.Ioc 0 t ×ˢ Set.Ioo (-1 : ℝ) 1).indicator (fun p => p.2)
  have hf : MemLp f 2 (volume.prod ν) :=
    levy_foundations_smallJumpBandMemLpTwo ν hν 0 t
  have hdef : LevyFoundations.smallJumpIntegralLp ν μ I hν t =
      I (hf.toLp f) := by
    unfold LevyFoundations.smallJumpIntegralLp
    change I (if h : MemLp f 2 (volume.prod ν) then h.toLp f else 0) =
      I (hf.toLp f)
    simp only [dif_pos hf]
  have hIso : ∀ g : Lp ℝ 2 (volume.prod ν),
      eLpNorm (I g) 2 μ = eLpNorm g 2 (volume.prod ν) := by
    intro g
    have hn := hI.norm_eq g
    rw [Lp.norm_def, Lp.norm_def] at hn
    exact (ENNReal.toReal_eq_toReal_iff'
      (Lp.eLpNorm_ne_top _) (Lp.eLpNorm_ne_top _)).mp hn
  calc
    (eLpNorm (LevyFoundations.smallJumpIntegralLp ν μ I hν t) 2 μ) ^ 2
        = (eLpNorm f 2 (volume.prod ν)) ^ 2 := by
          rw [hdef, hIso, eLpNorm_congr_ae (MemLp.coeFn_toLp hf)]
    _ = ENNReal.ofReal t *
        ∫⁻ x in Set.Ioo (-1) 1, ENNReal.ofReal (x ^ 2) ∂ν := by
          simpa only [sub_zero] using
            (ProbabilityTheory.eLpNorm_sq_bandFun (ν := ν)
              measurableSet_Ioo 0 t)
