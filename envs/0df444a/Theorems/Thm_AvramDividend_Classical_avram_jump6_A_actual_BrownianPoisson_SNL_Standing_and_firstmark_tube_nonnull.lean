-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_actual_BrownianPoisson_SNL_Standing_and_firstmark_tube_nonnull
-- name    : AvramDividend.Classical.avram_jump6_A_actual_BrownianPoisson_SNL_Standing_and_firstmark_tube_nonnull
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T19:09:01.016212+00:00
-- url     : https://prove2.me/theorems/347a2b29-cb0c-45f1-bd76-09e7b8ef6bc1
-- title:
--   Original physical Brownian-minus-negative-two-Poisson product has an actual Standing spectrally negative Lévy realisation and a strictly positive early first-mark Brownian tube event
-- statement:
--   The independently Proved genuine Brownian−2Poisson product Standing-model construction 1bd6705b and positive joint Brownian–Poisson first-negative-mark tube a714dadd combine on precisely the same μB×μJ probability space. Assuming the physical BrownianMotion W is realised by the source IsStdBMC path B so that its measured tube implies the small actual W path fluctuation, one obtains a genuine SpectrallyNegativeLevy X with actual path X_t=W_t−2N_t, σ=1, ν=δ−2, Standing, unbounded variation and finite negative-jump activity, simultaneously with a genuine strictly positive probability of 0<τ_0≤1/500 and uniformly small actual W_t. This is a concrete source bridge from the canonical stochastic product to the physical unit-mark ruin counterexample, beyond a synthetic arbitrary stochastic driver.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_GlynnSTS_NoAttain_Setting
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_actual_BrownianPoisson_SNL_Standing_and_firstmark_tube_nonnull
    {ΩB ΩJ : Type} [MeasurableSpace ΩB] [MeasurableSpace ΩJ]
    (μB : Measure ΩB) [IsProbabilityMeasure μB]
    (μJ : Measure ΩJ) [IsProbabilityMeasure μJ]
    (W : LevyStochCalc.Brownian.BrownianMotion μB)
    (N : ℝ≥0 → ΩJ → ℕ)
    (hBLevy : IsLevyProcess
      (fun t ω => W.W (t : ℝ) ω) μB)
    (hNLevy : IsLevyProcess
      (fun t ω => -(2 : ℝ) * (N t ω : ℝ)) μJ)
    (hBMeas : ∀ t : ℝ≥0,
      Measurable (fun ω => W.W (t : ℝ) ω))
    (hNMeas : ∀ t : ℝ≥0,
      Measurable (fun ω => -(2 : ℝ) * (N t ω : ℝ)))
    (hNRealMeas : ∀ t : ℝ≥0,
      Measurable (fun ω => (N t ω : ℝ)))
    (hNCountMeas : ∀ t : ℝ≥0, Measurable (N t))
    (hNCountLaw : ∀ t : ℝ≥0,
      μJ.map (N t) = poissonMeasure t)
    (hBCont : ∀ ω, Continuous
      (fun t : ℝ≥0 => W.W (t : ℝ) ω))
    (hNMono : ∀ ω, Monotone
      (fun t : ℝ≥0 => (N t ω : ℝ)))
    (hNRight : ∀ ω t, ContinuousWithinAt
      (fun s : ℝ≥0 => (N s ω : ℝ)) (Ici t) t)
    (hNLeft : ∀ ω t, 0 < t →
      ∃ l, Tendsto (fun s : ℝ≥0 => (N s ω : ℝ))
        (𝓝[<] t) (𝓝 l))
    (B : ΩB → C(unitInterval, ℝ))
    (hB : GlynnSTS.Limit.IsStdBMC μB B)
    (τ Y : ℕ → ΩJ → ℝ)
    (hJ : IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      (Measure.dirac (-2 : ℝ)) μJ)
    (hMatch : ∀ b : ΩB,
      (∀ s : unitInterval,
        s ≤ (⟨(1 / 500 : ℝ), by constructor <;> norm_num⟩ : unitInterval) →
          abs (B b s) < (1 / 4000 : ℝ)) →
      ∀ t : ℝ≥0, t ≤ 1 / 500 →
        abs (W.W (t : ℝ) b) < (1 / 4000 : ℝ)) :
    let G : ℝ≥0 → (ΩB × ΩJ) → ℝ :=
      fun t p => W.W (t : ℝ) p.1 - 2 * (N t p.2 : ℝ)
    ∃ (hStrong : ∀ t, StronglyMeasurable (G t))
      (X : SpectrallyNegativeLevy (μB.prod μJ)
        (Filtration.natural G hStrong)),
      X.X = G ∧ X.σ = 1 ∧
      X.ν = Measure.dirac (-2 : ℝ) ∧
      X.Standing ∧ ¬ X.BoundedVariation ∧
      X.ν ≠ 0 ∧ X.σ ≠ 0 ∧
      X.ν (Iio (0 : ℝ)) ≠ ⊤ ∧
      0 < (μB.prod μJ)
        {p : ΩB × ΩJ |
          (∀ t : ℝ≥0, t ≤ 1 / 500 →
            abs (W.W (t : ℝ) p.1) < (1 / 4000 : ℝ)) ∧
          0 < τ 0 p.2 ∧ τ 0 p.2 ≤ (1 / 500 : ℝ)} := by sorry
