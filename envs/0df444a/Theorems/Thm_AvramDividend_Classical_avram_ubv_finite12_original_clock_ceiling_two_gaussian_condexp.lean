-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_finite12_original_clock_ceiling_two_gaussian_condexp
-- name    : AvramDividend.Classical.avram_ubv_finite12_original_clock_ceiling_two_gaussian_condexp
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T11:29:32.327046+00:00
-- url     : https://prove2.me/theorems/6258d525-ad16-4beb-af40-2e3d208c1ec9
-- title:
--   Original zero-jump Gaussian optional sampling at arbitrary stopped physical-grid ceilings
-- statement:
--   For any bounded original right-continuous stopping clock and covered monotone mesh, construct a nearby actual sampled stopping index at which both original zero-jump Gaussian martingales are the stopped-history conditional expectations of their deterministic terminal-grid values. This combines physical clock localisation with source-exact linear and compensated quadratic sampling.
-- source:
--   Public Proved original clock ceiling 604909b0 and original two-stopping Gaussian conditional expectation a331e012. Explicit same original P, right-continuous filtration, source X; neither an unrelated Brownian motion nor an unproved Ito limit is substituted.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite12_arbitrary_clock_true_grid_ceiling
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite11_original_zerojump_two_stopped_grid_condexp

open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_finite12_original_clock_ceiling_two_gaussian_condexp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (σ : Ω → ℝ≥0)
    (hσ : IsStoppingTime 𝓕.rightCont (fun ω => (σ ω : WithTop ℝ≥0)))
    (e : ℕ → ℝ≥0) (he : Monotone e)
    (N : ℕ) (hN : ∀ ω, σ ω ≤ e N)
    (δ : ℝ≥0) (h0 : e 0 = 0)
    (hStep : ∀ i, e (i + 1) ≤ e i + δ)
    (𝓖 : Filtration ℕ mΩ) [SigmaFiniteFiltration P 𝓖]
    (h𝓖 : 𝓖 =
      ({ seq := fun i : ℕ => 𝓕.rightCont (e i)
         mono' := by
           intro i j hij
           exact 𝓕.rightCont.mono (he hij)
         le' := by
           intro i
           exact 𝓕.rightCont.le (e i) } : Filtration ℕ mΩ)) :
    let M : ℝ≥0 → Ω → ℝ := fun t ω => X.X t ω - (t : ℝ) * X.c
    let Q : ℝ≥0 → Ω → ℝ := fun t ω =>
      (M t ω) ^ 2 - (t : ℝ) * X.σ ^ 2
    ∃ (K : Ω → ℕ)
      (hK : IsStoppingTime 𝓖 (fun ω => (K ω : WithTop ℕ))),
      (∀ ω, (K ω : WithTop ℕ) ≤ (N : WithTop ℕ)) ∧
      (∀ ω, σ ω ≤ e (K ω) ∧ e (K ω) ≤ σ ω + δ) ∧
      (stoppedValue (fun i : ℕ => M (e i))
        (fun ω => (K ω : WithTop ℕ)) =ᵐ[P]
        P[stoppedValue (fun i : ℕ => M (e i))
          (fun _ : Ω => (N : WithTop ℕ)) | hK.measurableSpace]) ∧
      (stoppedValue (fun i : ℕ => Q (e i))
        (fun ω => (K ω : WithTop ℕ)) =ᵐ[P]
        P[stoppedValue (fun i : ℕ => Q (e i))
          (fun _ : Ω => (N : WithTop ℕ)) | hK.measurableSpace]) := by sorry
