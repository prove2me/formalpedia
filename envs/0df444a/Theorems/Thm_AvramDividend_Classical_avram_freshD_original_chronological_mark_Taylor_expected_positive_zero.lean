-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_freshD_original_chronological_mark_Taylor_expected_positive_zero
-- name    : AvramDividend.Classical.avram_freshD_original_chronological_mark_Taylor_expected_positive_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T14:18:17.270597+00:00
-- url     : https://prove2.me/theorems/71e1a06f-c792-4e74-8bbf-1365ef01fc37
-- title:
--   Actual original negative-jump chronological Taylor upper mesh error has vanishing expected positive part under physical count and weight bounds
-- statement:
--   For the actual original finite-activity spectrally negative Levy process and original left-continuous dividend strategy D, take a finite (possibly random) set S(omega) of actual negative jump times, all strictly positive, whose pre-jump reserves stay in a true compact positive cap-interior strip. Assume S(omega)'s cardinality is a.e. bounded by the original horizon-n negative-mark count N(omega). The source-faithful E_m is exactly the difference between the nonlinear negative-mark Taylor correction at the genuine post-right-payment mesh prestate and at the original true prejump reserve, for the same actual negative Levy mark. Proved 0174393a provides the pathwise convergence to zero of the *positive part of the signed chronological Taylor error sum*, even if a mark lands at zero where w has a jump. Under the independently declared a.e.-measurability and bounded-weight hypotheses, the sum positive part is dominated by L*N; the original negative-mark count N is Integrable by Proved e19df3d9. Mathlib dominated convergence yields the expected positive part converges to zero. This is a genuine chronological-mark, original-process stochastic-to-expected upper-limit bridge for 242ca5f1; a full physical cash identity and any assumed envelope derivation are still separate obligations.
-- source:
--   Original Avram Dividend Classical mixed sigma and entire negative Lévy jump cash-excess target 242ca5f1. Proved true original finite chronological negative mark time pathwise Taylor upper-limit 0174393a and true entire finite-activity negative count L1 e19df3d9; actual initial capital x, dividend D, jump X retained.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_freshD_original_fullnegative_physical_finite_horizon_count_L1
import Theorems.Thm_AvramDividend_Classical_avram_freshD_original_true_finite_mark_times_grid_prestates_Taylor_upperlim
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_freshD_original_chronological_mark_Taylor_expected_positive_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (c : ℝ)
    (hc : 0 < c) (hcC : ENNReal.ofReal c ≤ C)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw0 : 0 ≤ w 0) (hwcont : ContinuousOn w (Ici (0 : ℝ)))
    (hwneg : ∀ y : ℝ, y < 0 → w y = 0)
    (n : ℕ) (S : Ω → Finset ℝ≥0)
    (hSpos : ∀ ω t, t ∈ S ω → 0 < t)
    (hSneg : ∀ ω t, t ∈ S ω →
      X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t < 0)
    (hSinterior : ∀ ω t, t ∈ S ω →
      x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) t - D t ω ∈
        Ioo (0 : ℝ) c)
    (hCount : ∀ᵐ ω ∂P, ((S ω).card : ℝ) ≤
      (((Measure.count.restrict {t : ℝ≥0 |
        0 < t ∧ X.X t ω -
        Function.leftLim (fun r : ℝ≥0 => X.X r ω) t ≠ 0}).map
          (fun t : ℝ≥0 => (t,
            X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t)))
          (Ioc 0 (n : ℝ≥0) ×ˢ Iio (0 : ℝ))).toReal)
    (grid : ℕ → Ω → ℝ≥0 → ℝ≥0)
    (hgrid : ∀ᵐ ω ∂P, ∀ t ∈ S ω,
      Tendsto (fun m => grid m ω t) atTop (𝓝[<] t))
    (E : ℕ → Ω → ℝ≥0 → ℝ)
    (hEsource : ∀ m ω t,
      E m ω t =
        let y := x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) t -
          D t ω
        let z := X.X t ω -
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) t
        let u := x + X.X (grid m ω t) ω -
          rightLimit D (grid m ω t) ω
        ((w (u + z) - w u -
          (if -1 < z then z * deriv w u else 0)) -
         (w (y + z) - w y -
          (if -1 < z then z * deriv w y else 0))))
    (L : ℝ) (hL : 0 ≤ L)
    (hBound : ∀ m ω t, t ∈ S ω → |E m ω t| ≤ L)
    (hMeas : ∀ m, AEStronglyMeasurable
      (fun ω => max (∑ t ∈ S ω, E m ω t) 0) P) :
    Tendsto
      (fun m => ∫ ω, max (∑ t ∈ S ω, E m ω t) 0 ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
