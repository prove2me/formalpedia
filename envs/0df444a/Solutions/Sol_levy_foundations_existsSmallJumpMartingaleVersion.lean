-- Prove2me | solution 1 for levy_foundations_existsSmallJumpMartingaleVersion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T20:12:49.011054+00:00
-- url     : https://prove2.me/submissions/c3ce3af0-116f-4672-82d6-24232fe30a01

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonCompensated
import Definitions.Def_LeanLevy_RandomMeasure_PoissonMartingale
import Definitions.Def_levy_foundations_prmFiltration
import Definitions.Def_levy_foundations_smallJumpIntegralLp
import Definitions.Def_levy_foundations_isPoissonPointFamily
import Definitions.Def_levy_foundations_isCompensatedPoissonL2Extension
import Theorems.Thm_ProbabilityTheory_integral_compensatedPoissonIntegral
import Theorems.Thm_ProbabilityTheory_levyCompensatedSmallJumpVersion_ae_eq
import Theorems.Thm_ProbabilityTheory_martingale_levyCompensatedSmallJump
import Theorems.Thm_levy_foundations_compensatedPoissonL2ExtensionUnique
import Theorems.Thm_levy_foundations_smallJumpMemLpTwo

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- Transfer the original compensated-Poisson martingale along L²-extension uniqueness. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (ν : Measure ℝ) [SigmaFinite ν]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → ℝ × ℝ)
    (hd : LevyFoundations.IsPoissonPointFamily K X (volume.prod ν) μ)
    (hν : LevyFoundations.isLevyMeasure ν)
    (I : Lp ℝ 2 (volume.prod ν) → Lp ℝ 2 μ)
    (hI : LevyFoundations.IsCompensatedPoissonL2Extension
      (volume.prod ν) μ K X I) :
    ∃ Y : ℝ≥0 → Ω → ℝ,
      (∀ t : ℝ≥0,
        Y t =ᵐ[μ] (fun ω =>
          LevyFoundations.smallJumpIntegralLp ν μ I hν (t : ℝ) ω)) ∧
      MeasureTheory.Martingale Y
        (LevyFoundations.prmFiltration K X ν
          hd.measurable_count hd.measurable_point) μ := by
  let hd' : ProbabilityTheory.IsPoissonPointFamily K X (volume.prod ν) μ :=
    ⟨hd.measurable_count, hd.measurable_point, hd.indep, hd.law_count, hd.law_point⟩
  let I0 : Lp ℝ 2 (volume.prod ν) → Lp ℝ 2 μ :=
    ProbabilityTheory.compensatedPoissonIntegral hd'
  have hadd : ∀ f g : Lp ℝ 2 (volume.prod ν), I0 (f + g) = I0 f + I0 g :=
    fun f g => ProbabilityTheory.compensatedPoissonIntegral_add hd' f g
  have hnorm : ∀ f : Lp ℝ 2 (volume.prod ν), ‖I0 f‖ = ‖f‖ :=
    fun f => ProbabilityTheory.norm_compensatedPoissonIntegral hd' f
  let F : Lp ℝ 2 (volume.prod ν) →+ Lp ℝ 2 μ :=
    { toFun := I0
      map_zero' := by
        apply norm_eq_zero.mp
        simpa using hnorm (0 : Lp ℝ 2 (volume.prod ν))
      map_add' := hadd }
  have hcont : Continuous (F : Lp ℝ 2 (volume.prod ν) → Lp ℝ 2 μ) := by
    have hiso : Isometry F := by
      apply (isometry_iff_dist_eq).2
      intro f g
      calc
        dist (F f) (F g) = ‖F f - F g‖ := dist_eq_norm _ _
        _ = ‖F (f - g)‖ := by rw [map_sub]
        _ = ‖f - g‖ := hnorm _
        _ = dist f g := (dist_eq_norm _ _).symm
    exact hiso.continuous
  have hcanon : LevyFoundations.IsCompensatedPoissonL2Extension
      (volume.prod ν) μ K X I0 := by
    refine ⟨hadd, ?_, hnorm, ?_, ?_⟩
    · intro c f
      change F (c • f) = c • F f
      exact map_real_smul F hcont c f
    · intro f
      exact ProbabilityTheory.integral_compensatedPoissonIntegral hd' f
    · intro f hf hf1 hf2
      change (fun ω => ProbabilityTheory.compensatedPoissonIntegral hd' (hf2.toLp f) ω)
        =ᵐ[μ] ProbabilityTheory.compensatedPoissonSum K X f (volume.prod ν)
      exact ProbabilityTheory.compensatedPoissonIntegral_eq_sum hd' hf hf1 hf2
  have hIeq : I = I0 :=
    levy_foundations_compensatedPoissonL2ExtensionUnique
      (volume.prod ν) μ K X I I0 hI hcanon
  have hν' : ProbabilityTheory.IsLevyMeasure ν := hν
  have hLp (t : ℝ) :
      LevyFoundations.smallJumpIntegralLp ν μ I hν t =
        ProbabilityTheory.levyCompensatedSmallJump hd' hν' t := by
    rw [hIeq]
    unfold LevyFoundations.smallJumpIntegralLp ProbabilityTheory.levyCompensatedSmallJump
    dsimp only
    simp only [dif_pos (levy_foundations_smallJumpMemLpTwo ν hν t)]
    all_goals dsimp [I0]
    all_goals rfl
  refine ⟨ProbabilityTheory.levyCompensatedSmallJumpVersion hd' hν', ?_, ?_⟩
  · intro t
    calc
      ProbabilityTheory.levyCompensatedSmallJumpVersion hd' hν' t
          =ᵐ[μ] (fun ω => ProbabilityTheory.levyCompensatedSmallJump hd' hν' (t : ℝ) ω) :=
            ProbabilityTheory.levyCompensatedSmallJumpVersion_ae_eq hd' hν' t
      _ =ᵐ[μ] (fun ω => LevyFoundations.smallJumpIntegralLp ν μ I hν (t : ℝ) ω) := by
        rw [hLp (t : ℝ)]
  · exact ProbabilityTheory.martingale_levyCompensatedSmallJump hd' hν'
