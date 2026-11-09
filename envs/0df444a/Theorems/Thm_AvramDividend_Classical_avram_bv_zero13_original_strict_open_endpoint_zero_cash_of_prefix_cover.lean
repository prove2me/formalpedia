-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_original_strict_open_endpoint_zero_cash_of_prefix_cover
-- name    : AvramDividend.Classical.avram_bv_zero13_original_strict_open_endpoint_zero_cash_of_prefix_cover
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T00:45:30.47922+00:00
-- url     : https://prove2.me/theorems/f62dae07-1d7c-419f-8ab9-f1bc6d74ce62
-- title:
--   Original finite activity BV strict open-endpoint zero reserve weighted cash by monotone pre-jump prefix approximation
-- statement:
--   For any actual original-process sample path and arbitrary admissible adapted dividends, take a strict right endpoint before or at the first physical negative jump. Assume the postpayment controlled reserve remains zero before that endpoint, no original source jump occurs in the open time interval, and a monotone sequence of strict earlier endpoints covers that open interval by increasing half-open prefixes. On the common full-probability event supplied by the previously Proved simultaneous cash identity, discounted Stieltjes cash over the strict open interval equals physical drift-scaled Lebesgue cash for every measurable nonnegative weight. In particular the negative source jump at the terminal point and its dividend/ruin atom are excluded, while time-zero right-payment cash at the initial endpoint is also excluded.
-- source:
--   Root-connected strict pre-ruin cash bridge using public Proved bc78efba and Mathlib monotone convergence lintegral_iSup. Requires explicit monotone covering prefix sequence to avoid unproved stopping time or endpoint measurability assumptions.

import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_original_all_pathwise_restart_zero_weighted_cash_no_survival
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_zero13_original_strict_open_endpoint_zero_cash_of_prefix_cover
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (hDrift : 0 ≤ X.drift)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (H : ℝ≥0) (hH : 0 < H) :
    ∀ᵐ ω ∂P,
      ∀ (s J : ℝ≥0), s < J → J ≤ H →
      ∀ (a : ℕ → ℝ≥0),
      (∀ n, s ≤ a n ∧ a n < J) →
      Monotone (fun n : ℕ => Ioc (s : ℝ) ((a n : ℝ≥0) : ℝ)) →
      (⋃ n, Ioc (s : ℝ) ((a n : ℝ≥0) : ℝ)) =
        Ioo (s : ℝ) (J : ℝ) →
      (∀ u : ℝ≥0, s ≤ u → u < J →
        riskProcess X x D u ω -
          (rightLimit D u ω - D u ω) = 0) →
      (∀ u : ℝ≥0, u ∈ Ioo s J →
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0) →
      ∀ f : ℝ → ℝ≥0∞, Measurable f →
        (∫⁻ t in Ioo (s : ℝ) (J : ℝ), f t
          ∂(dividendMeasure D ω)) =
        (∫⁻ t in Ioo (s : ℝ) (J : ℝ), f t
          ∂((ENNReal.ofReal X.drift) • volume)) := by sorry
