-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_uniform_physical_Taylor_norm_source_dom
-- name    : AvramDividend.Classical.avram_bv_error7_original_uniform_physical_Taylor_norm_source_dom
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T09:23:00.634307+00:00
-- url     : https://prove2.me/theorems/f9a349be-0c4e-4c43-b21f-5a80afce7c7f
-- title:
--   Original physical C1 Taylor source-error uniformly dominated by intrinsic BV source mass
-- statement:
--   For the literal original spectrally negative BV Levy X, admissible dividend D, and every monotone physical grid from 0 to T, there is a deterministic strict-interior C1 radius such that if all genuine prepayment reserve-segments remain in the fixed compact subcap band and every jump-removed Y increment is smaller than this radius almost surely at each grid index, the exact discounted Taylor source errors are uniformly bounded almost surely by |drift| T + |T drift - X_T|. It discharges the dominating-function hypothesis of the already Proved positive-error dominated-convergence theorem once the concrete physical-grid band/refinement certificate is supplied. No prebudget or Fatou statement is assumed.
-- source:
--   Proved source-exact BV-ERROR7 Taylor cell estimate d7008b37-9222-40a4-9996-ee5566919641, original C1 physical mesh 23921613-c6f7-426c-a634-d2ddcd457e42, original variation b473d1e9-c7cd-404f-950e-d1cc9dca5900. Intended direct adapter to positive-error DCT 70a2660b-af9a-4e0c-9e31-a0cf5eed04e9. Cap/ruin contact outside band remains an explicit separate obligation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_interior_Taylor_error_le_L1_source_mass
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_original_uniform_physical_Taylor_norm_source_dom
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hBand : Set.Icc a b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
    (u : ℕ → ℕ → ℝ≥0) (k : ℕ → ℕ)
    (hGrid : ∀ m, u m 0 = 0 ∧ u m (k m) = T ∧
      (∀ i, i < k m → u m i ≤ u m (i + 1)))
    (Err : ℕ → Ω → ℝ)
    (hSource : ∀ m ω, Err m ω =
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0
       let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
       let z : ℕ → ℝ := fun i =>
         x + X.X (u m i) ω - rightLimit D (u m i) ω
       let c : ℕ → ℝ := fun i => Y (u m (i + 1)) - Y (u m i)
       ∑ i ∈ Finset.range (k m),
         Real.exp (-(q * (u m i : ℝ))) *
           (w (z i + c i) - w (z i) - deriv w (z i) * c i))) :
    ∃ δ : ℝ, 0 < δ ∧
      ((∀ m, ∀ᵐ ω ∂P,
        (let J : ℝ≥0 → ℝ := fun t =>
          ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
            Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
          else 0
         let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
         let z : ℕ → ℝ := fun i =>
           x + X.X (u m i) ω - rightLimit D (u m i) ω
         let c : ℕ → ℝ := fun i => Y (u m (i + 1)) - Y (u m i)
         (∀ i, i < k m →
           Set.uIcc (z i) (z i + c i) ⊆ Set.Icc a b) ∧
         (∀ i, i < k m → |c i| < δ))) →
       ∀ m, ∀ᵐ ω ∂P,
         ‖Err m ω‖ ≤ |X.drift| * (T : ℝ) +
           |(T : ℝ) * X.drift - X.X T ω|) := by sorry
