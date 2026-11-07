-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_physical_C1_positive_error_L1_of_variation_bound
-- name    : AvramDividend.Classical.avram_bv_error7_original_physical_C1_positive_error_L1_of_variation_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T08:44:34.441788+00:00
-- url     : https://prove2.me/theorems/70a2660b-af9a-4e0c-9e31-a0cf5eed04e9
-- title:
--   Actual original BV discounted physical C1 positive error has vanishing mean under intrinsic source variation envelope
-- statement:
--   The finite-grid Taylor error is defined by the literal original controlled Lévy X, admissible dividend D, right-payment reserve, actual negative-jump sum J, jump-removed physical process Y and discounted C1 cell commutators. Up to a unit physical horizon, an a.e. bound by a fixed multiple of the true drift/source variation provides an integrable dominating mass automatically from the original BV first-moment theorem. Together with a.e. error convergence and measurable errors this yields both integrability of their positive parts and vanishing expected positive error by Bochner dominated convergence. The source-bound estimate itself remains a separate cell/contact/localisation obligation; no canonical Open budget is imported.
-- source:
--   Authoritative Proved original source-variation envelope 09287ead-652a-4521-8a54-ac198d1c917b (ACCEPTED candidate 29383); initial authoring job 93b01b21-edda-46d8-a048-78503ced9eb3 failed only because this dependency was Open at its publication time. Proved original C1 error cf5b9fb6, pathwise physical refinement 499ae160 and 8442e7aa; Proved 9831126a establishes the physical source first moment. No circular dependency on 2bc848f9 or canonical budget.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_BV_source_variation_L1_upto_one
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_original_physical_C1_positive_error_L1_of_variation_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (T : ℝ≥0) (hT : T ≤ 1)
    (u : ℕ → ℕ → ℝ≥0) (k : ℕ → ℕ)
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
           (w (z i + c i) - w (z i) - deriv w (z i) * c i)))
    (K : ℝ) (hK : 0 ≤ K)
    (hErrMeas : ∀ m, AEStronglyMeasurable (Err m) P)
    (hErrAE : ∀ᵐ ω ∂P,
      Tendsto (fun m => Err m ω) atTop (nhds (0 : ℝ)))
    (hDom : ∀ m, ∀ᵐ ω ∂P,
      ‖Err m ω‖ ≤ K * (|X.drift| * (T : ℝ) +
        |(T : ℝ) * X.drift - X.X T ω|)) :
    (∀ m, Integrable (fun ω => max (Err m ω) 0) P) ∧
    Tendsto (fun m => ∫ ω, max (Err m ω) 0 ∂P)
      atTop (nhds (0 : ℝ)) := by sorry
