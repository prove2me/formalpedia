-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_finite_predictable_grid_from_conditional_diagonals
-- name    : AvramDividend.Classical.avram_p4_g_isometry_original_finite_predictable_grid_from_conditional_diagonals
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:38:38.095417+00:00
-- url     : https://prove2.me/theorems/dc29fab5-069b-4b42-b8e5-1ba3b9a690bb
-- title:
--   Original intrinsic finite-grid predictable L2 isometry with original conditional count variance
-- statement:
--   Finite sums of physical intrinsic negative-band compensated jump counts, with original F_i-predictable H_i and true X.nu rates, satisfy E[(sum_i H_i d(N_X-dt nu))²] = sum_i r_i E[H_i²]. Off-diagonal cancellation follows from the already Proved original P2-E rectangle law, while conditional physical second-moment, predictable-prefix measurability, product L2 and integrability are explicit assumptions. No Poisson replacement, infinite-band limit or stopped martingale claim.
-- source:
--   Proved P2-E canonical 393b03a8, P4-G cross ca34b7de and diagonal 9b483610, physical original X.X and X.nu.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_past_cross_zero_from_proved_compensator
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_raw_diagonal_of_source_second_rectangle

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal Nat BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_g_isometry_original_finite_predictable_grid_from_conditional_diagonals
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (ε : ℝ) (hε : 0 < ε) (B : ℕ → Set ℝ)
    (hB : ∀ i, MeasurableSet (B i))
    (hBand : ∀ i, B i ⊆ Ioo (-1 : ℝ) (-ε))
    (hν : ∀ i, X.ν (B i) < ⊤)
    (N : ℕ → Ω → ℝ≥0∞)
    (hActual : ∀ i, N i = fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (grid i) (grid (i + 1)) ×ˢ B i))
    (hMeas : ∀ i, Measurable (N i))
    (r : ℕ → ℝ)
    (hRate : ∀ i, r i =
      (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)).toReal)
    (H D : ℕ → Ω → ℝ)
    (hD : ∀ i ω, D i ω = H i ω * ((N i ω).toReal - r i))
    (hH : ∀ i, StronglyMeasurable[𝓕 (grid i)] (H i))
    (hPrefix : ∀ i, StronglyMeasurable[𝓕 (grid i)]
      (fun ω => ∑ j ∈ Finset.range i, D j ω))
    (hPairL2 : ∀ i, MemLp (fun ω =>
      (∑ j ∈ Finset.range i, D j ω) * H i ω) 2 P)
    (hCountL2 : ∀ i, MemLp (fun ω =>
      (N i ω).toReal - r i) 2 P)
    (hSecond : ∀ i, P[(fun ω => ((N i ω).toReal - r i) ^ 2)
      | 𝓕 (grid i)] =ᵐ[P] (fun _ => r i))
    (hSq : ∀ i, Integrable (fun ω =>
      ((N i ω).toReal - r i) ^ 2) P)
    (hHSq : ∀ i, Integrable (fun ω => (H i ω) ^ 2) P)
    (hWSq : ∀ i, Integrable (fun ω =>
      (H i ω) ^ 2 * ((N i ω).toReal - r i) ^ 2) P)
    (hPrefixSq : ∀ i, Integrable (fun ω =>
      (∑ j ∈ Finset.range i, D j ω) ^ 2) P)
    (n : ℕ) :
    (∫ ω, (∑ i ∈ Finset.range n, D i ω) ^ 2 ∂P) =
      ∑ i ∈ Finset.range n, r i * ∫ ω, (H i ω) ^ 2 ∂P := by sorry
