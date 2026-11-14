-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b38_original_varying_good_bad_stopped_taylor_with_zero
-- name    : AvramDividend.Classical.avram_b38_original_varying_good_bad_stopped_taylor_with_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T08:50:25.58477+00:00
-- url     : https://prove2.me/theorems/d78be92e-d296-40bd-99c5-4f7c5ffdb555
-- title:
--   Original varying-good-band stopped Taylor error vanishes allowing zero increments
-- statement:
--   For genuine original stopped Levy physical C2 meshes in compact good bands that eventually cover almost every path, with a common expected square-energy bound and an integrable bad-event envelope, the expected sum of errors vanishes, including zero increments.
-- source:
--   B36 original zero-cell C2 modulus and A06 bad-event dominated convergence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_b36_original_random_stopped_C2_Taylor_L1_allow_zero_increments
import Theorems.Thm_AvramDividend_Classical_avram_a06_masked_bad_event_integral_vanish_of_ae_eventual_good
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_b38_original_varying_good_bad_stopped_taylor_with_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbcap : ENNReal.ofReal b < C) :
    ∀ (A : ℕ → Set Ω) (S : ℕ → Finset ℕ)
      (s t : ℕ → ℕ → Ω → ℝ≥0),
      let z : ℕ → Ω → ℕ → ℝ := fun m ω i =>
        Function.leftLim (fun u : ℝ≥0 =>
          x + X.X u ω - rightLimit D u ω) (s m i ω)
      let g : ℕ → Ω → ℕ → ℝ := fun m ω i =>
        X.X (t m i ω) ω - X.X (s m i ω) ω -
          ((t m i ω : ℝ) - (s m i ω : ℝ)) * X.c
      let Q : ℕ → Ω → ℝ := fun m ω => ∑ i ∈ S m, (g m ω i) ^ 2
      let R : ℕ → Ω → ℝ := fun m ω => ∑ i ∈ S m,
        (w (z m ω i + g m ω i) -
          taylorWithinEval w 1
            (Set.uIcc (z m ω i) (z m ω i + g m ω i))
            (z m ω i) (z m ω i + g m ω i) -
          (iteratedDeriv 2 w (z m ω i) * (g m ω i) ^ 2) / 2)
      (∀ m, MeasurableSet (A m)) →
      (∀ᵐ ω ∂P, ∀ᶠ m in atTop, ω ∈ A m) →
      (∀ m i, i ∈ S m → IsStoppingTime 𝓕.rightCont
        (fun ω => (s m i ω : WithTop ℝ≥0))) →
      (∀ m i, i ∈ S m → IsStoppingTime 𝓕.rightCont
        (fun ω => (t m i ω : WithTop ℝ≥0))) →
      (∀ m, ∀ᵐ ω ∂(P.restrict (A m)), ∀ i ∈ S m,
        z m ω i ∈ Icc a b ∧ z m ω i + g m ω i ∈ Icc a b) →
      (∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ m, N ≤ m →
        ∀ᵐ ω ∂(P.restrict (A m)), ∀ i ∈ S m,
          dist (z m ω i + g m ω i) (z m ω i) < δ) →
      (∀ m, AEStronglyMeasurable (fun ω => |R m ω|) (P.restrict (A m))) →
      ∀ K : ℝ, 0 ≤ K →
        (∀ m, (∫ ω in A m, Q m ω ∂P) ≤ K) →
        ∀ H : Ω → ℝ, Measurable H → Integrable H P →
        ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ m, N ≤ m →
          IntegrableOn (fun ω => |R m ω|) (A m) P ∧
          (∫ ω in A m, |R m ω| ∂P) +
          (∫ ω, if ω ∈ A m then (0 : ℝ) else H ω ∂P) ≤ η := by sorry
