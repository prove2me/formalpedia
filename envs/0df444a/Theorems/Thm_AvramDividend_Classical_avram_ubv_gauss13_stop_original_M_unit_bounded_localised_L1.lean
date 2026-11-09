-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_stop_original_M_unit_bounded_localised_L1
-- name    : AvramDividend.Classical.avram_ubv_gauss13_stop_original_M_unit_bounded_localised_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T00:17:06.744923+00:00
-- url     : https://prove2.me/theorems/33a198b6-0602-4cc4-8f15-37a767b26179
-- title:
--   Original linear Gaussian physical-clock L1 limit with unit-bounded localised multipliers
-- statement:
--   Original same-process zero-jump Gaussian linear source complement to public Proved quadratic 59e1e063, needed for finite-cap C2 physical reward consumer a338c453-58c0-411c-aaca-5cec689ed807 and top-cap positive-clock witness 249c532d-4ec0-498c-81f0-b380dd476344. If each original centred linear source M(T_n) is the conditional expectation of one fixed integrable original M(B) with respect to the sampled true stopped history, and converges almost everywhere at physical stopped sigma, then unit-bounded, measurable and almost-surely convergent compact original coefficients preserve the L1 limit. Reuses same original filtration and avoids floor-of-stopping-time assumptions. This is analytic source limit only; actual dividend ledger remains a separate obligation.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gauss13_stop_original_M_unit_bounded_localised_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (M : ℝ≥0 → Ω → ℝ)
    (hMsource : ∀ t ω, M t ω =
      X.X t ω - (t : ℝ) * X.c)
    (B : ℝ≥0) (hMB : Integrable (M B) P)
    (σ : Ω → ℝ≥0) (T : ℕ → Ω → ℝ≥0)
    (ℋ : ℕ → MeasurableSpace Ω)
    (hℋ : ∀ n, ℋ n ≤ mΩ)
    (hCE : ∀ n, (fun ω => M (T n ω) ω) =ᵐ[P]
      condExp (ℋ n) P (M B))
    (hAE : ∀ᵐ ω ∂P,
      Tendsto (fun n => M (T n ω) ω) atTop
        (nhds (M (σ ω) ω)))
    (G : ℕ → Ω → ℝ) (g : Ω → ℝ)
    (hGmeas : ∀ n, AEStronglyMeasurable (G n) P)
    (hGunit : ∀ n ω, ‖G n ω‖ ≤ 1)
    (hGae : ∀ᵐ ω ∂P, Tendsto (fun n => G n ω) atTop (nhds (g ω))) :
    Tendsto (fun n =>
      eLpNorm (fun ω => G n ω * M (T n ω) ω -
        g ω * M (σ ω) ω) 1 P)
      atTop (nhds 0) := by
  sorry
