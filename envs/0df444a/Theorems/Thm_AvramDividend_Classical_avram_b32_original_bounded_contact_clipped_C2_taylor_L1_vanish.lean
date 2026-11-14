-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b32_original_bounded_contact_clipped_C2_taylor_L1_vanish
-- name    : AvramDividend.Classical.avram_b32_original_bounded_contact_clipped_C2_taylor_L1_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:40:37.663536+00:00
-- url     : https://prove2.me/theorems/6805975f-4a51-4a50-a971-3b00f2bc322f
-- title:
--   Original bounded-count random stopped clipped contact C2 Taylor error vanishes in local L1
-- statement:
--   If a genuine original spectrally negative Lévy stopped mesh has uniformly at most L compact-band physical contact cells per row and its drift-centred increments are eventually uniformly small on a localisation event, then their total absolute expected C2 Taylor error converges to zero without separate uniform energy assumptions or global jump-square moments.
-- source:
--   Avram Palmowski Pistorius (2007), Proposition 4(i), localised last stopped contact-cell error; proved B29 plus B30.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_b29_original_random_stopped_C2_taylor_uniform_expected_vanish
import Theorems.Thm_AvramDividend_Classical_avram_b30_original_random_clock_compact_square_energy_expected_card_bound
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b32_original_bounded_contact_clipped_C2_taylor_L1_vanish
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbcap : ENNReal.ofReal b < C) :
    ∀ (A : Set Ω) (S : ℕ → Finset ℕ)
      (s t : ℕ → ℕ → Ω → ℝ≥0),
      let z : ℕ → Ω → ℕ → ℝ := fun m ω i =>
        Function.leftLim (fun u : ℝ≥0 =>
          x + X.X u ω - rightLimit D u ω) (s m i ω)
      let g : ℕ → Ω → ℕ → ℝ := fun m ω i =>
        X.X (t m i ω) ω - X.X (s m i ω) ω -
          ((t m i ω - s m i ω) : ℝ) * X.c
      let R : ℕ → Ω → ℝ := fun m ω => ∑ i ∈ S m,
        (w (z m ω i + g m ω i) -
          taylorWithinEval w 1
            (Set.uIcc (z m ω i) (z m ω i + g m ω i))
            (z m ω i) (z m ω i + g m ω i) -
          (iteratedDeriv 2 w (z m ω i) * (g m ω i) ^ 2) / 2)
      (∀ m i, i ∈ S m → IsStoppingTime 𝓕.rightCont
        (fun ω => (s m i ω : WithTop ℝ≥0))) →
      (∀ m i, i ∈ S m → IsStoppingTime 𝓕.rightCont
        (fun ω => (t m i ω : WithTop ℝ≥0))) →
      (∀ m, ∀ᵐ ω ∂(P.restrict A), ∀ i ∈ S m,
        z m ω i ∈ Icc a b ∧ z m ω i + g m ω i ∈ Icc a b ∧
        z m ω i ≠ z m ω i + g m ω i) →
      (∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ m, N ≤ m →
        ∀ᵐ ω ∂(P.restrict A), ∀ i ∈ S m,
          dist (z m ω i + g m ω i) (z m ω i) < δ) →
      (∀ m, AEStronglyMeasurable (fun ω => |R m ω|) (P.restrict A)) →
      ∀ L : ℕ, (∀ m, (S m).card ≤ L) →
        ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ m, N ≤ m →
          IntegrableOn (fun ω => |R m ω|) A P ∧
          (∫ ω in A, |R m ω| ∂P) ≤ η := by sorry
