-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_p1_actual_controlled_clipped_grid_l2_limit_mean_zero
-- name    : AvramDividend.Classical.avram_wave5_p1_actual_controlled_clipped_grid_l2_limit_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T00:47:33.217234+00:00
-- url     : https://prove2.me/theorems/9edde1b5-9b3d-4dbb-a7f8-098e172cd9b8
-- title:
--   Actual controlled ruin-stopped clipped Lévy grid martingales admit a centred L² limit under explicit tail energy
-- statement:
--   On the unchanged SpectrallyNegativeLevy X, original probability P, and actually adapted dividend control D, construct each finite-grid centred clipped source-increment sum with the true discounted, ruin-stopped verification derivative. Given its exact L²(P) representation, a source-specific finite-band energy envelope and the explicit square-energy tail bound, the sequence converges in L²(P) to an integrable mean-zero limit. The finite-grid centring is proved from the accepted original-source stopped clipped grid theorem, not postulated. The result does not establish source jump-count compensation, continuous-time Itô–Meyer or the energy bound automatically.
-- source:
--   Avram Dividend controlled stopped martingale limit; genuine source-specific bridge from Proved 090ca3ef-3f23-445b-9279-d48c4f126241 and 540bd939-b21d-4883-901a-fc40fbf58ec6. Root mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43. Source closure leaves future joint PRM and controlled Ito–Meyer to Chat 01/03.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_originalStoppedDerivative_compensatedClippedFiniteGrid_mean_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_actual_probability_l2_stopped_band_limit_mean_zero

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_p1_actual_controlled_clipped_grid_l2_limit_mean_zero
    {Ω α ι : Type*} [mΩ : MeasurableSpace Ω] [mα : MeasurableSpace α]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q K : ℝ) (hK : 0 ≤ K)
    (T : ℝ≥0)
    (S : ℕ → Finset ι) (s t : ℕ → ι → ℝ≥0)
    (hst : ∀ n i, i ∈ S n → s n i ≤ t n i)
    (R : ℕ → ι → ℝ)
    (hR : ∀ n i, i ∈ S n → 0 ≤ R n i)
    (F : ℕ → Ω → ℝ)
    (hF : ∀ n, F n =
      (fun ω => ∑ i ∈ S n,
        max (-K) (min K
          (if s n i ≤ T then
            (Real.exp (-(q * (s n i : ℝ))) *
              deriv w (Function.leftLim
                (fun u : ℝ≥0 =>
                  x + X.X u ω - rightLimit D u ω) (s n i))) *
            (if (s n i : ℝ≥0∞) ≤ ruinTime X x D ω then
              (1 : ℝ) else 0)
          else 0)) *
        (max (-R n i) (min (R n i)
          (X.X (t n i) ω - X.X (s n i) ω)) -
          ∫ η, max (-R n i) (min (R n i)
            (X.X (t n i - s n i) η)) ∂P)))
    (μ : Measure α) (f : α → ℝ) (hf : Measurable f)
    (henergy : ∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ) ∂μ < ∞)
    (B : ℕ → Set α) (hB : ∀ n, MeasurableSet (B n))
    (hBfinite : ∀ n, μ (B n) < ∞)
    (hBmono : Monotone B) (hBcover : (⋃ n, B n) = Set.univ)
    (M : ℕ → Lp ℝ (2 : ℝ≥0∞) P)
    (hRep : ∀ n, (M n : Ω → ℝ) =ᵐ[P] F n)
    (hbound : ∀ m n, m ≤ n →
      dist (M m) (M n) ≤
        (eLpNorm ((B m)ᶜ.indicator f) (2 : ℝ≥0∞) μ).toReal) :
    ∃ Mlimit : Lp ℝ (2 : ℝ≥0∞) P,
      Tendsto M Filter.atTop (nhds Mlimit) ∧
      (∫ ω, Mlimit ω ∂P) = 0 := by sorry
