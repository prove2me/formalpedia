-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_anoise35_original_dyadic_finite_simple_condexp
-- name    : AvramDividend.Classical.avram_anoise35_original_dyadic_finite_simple_condexp
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T13:09:32.42321+00:00
-- url     : https://prove2.me/theorems/dd554a61-6ec6-4cd4-aa77-bfcbb3863941
-- title:
--   Original dyadic signed marked-count approximants are integrable and right-continuously centred
-- statement:
--   For the actual original spectrally negative Levy process with finite negative-mark intensity, every dyadic finite-simple compensated signed marked-count approximation over a deterministic future interval is integrable and has conditional expectation zero given the original right-continuous filtration at its left endpoint. This is the finite-step stochastic part of the source-exact dyadic approximation, using proved original finite-simple conditional centring 6de0a6db.
-- source:
--   One necessary conjunct pair of root-connected Open 4da238cd. Copies the original marked-count dyadic source exactly, retaining original filtration and all endpoint conventions. Companion physical approximation child anoise36 handles its distinct analytic and measure-convergence obligations.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_anoise35_original_dyadic_finite_simple_condexp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ n : ℕ, ∀ s t : ℝ≥0, s ≤ t →
      let B : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))
      let C : ℕ → ℕ → Set ℝ := fun k i =>
        B ∩ Ioc (-1 + (i : ℝ) / (2 : ℝ) ^ k)
          (-1 + ((i : ℝ) + 1) / (2 : ℝ) ^ k)
      let J : ℕ → ℕ → Ω → ℝ≥0∞ := fun k i ω =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ C k i)
      let M : ℕ → Ω → ℝ := fun k ω =>
        ∑ i ∈ Finset.range (2 ^ k),
          (-1 + (i : ℝ) / (2 : ℝ) ^ k) *
            ((J k i ω).toReal -
              (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (C k i)).toReal)
      (∀ k, Integrable (M k) P) ∧
      (∀ k, P[M k | 𝓕.rightCont s] =ᵐ[P] (fun _ => (0 : ℝ))) := by sorry
