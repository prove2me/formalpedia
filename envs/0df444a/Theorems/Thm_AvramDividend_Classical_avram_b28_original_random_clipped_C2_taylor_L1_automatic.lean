-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b28_original_random_clipped_C2_taylor_L1_automatic
-- name    : AvramDividend.Classical.avram_b28_original_random_clipped_C2_taylor_L1_automatic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T23:54:32.925277+00:00
-- url     : https://prove2.me/theorems/86c1be04-4443-45d4-917b-1da49ccae75e
-- title:
--   Original random stopped C2 Taylor compact mesh remainder is locally integrable and bounded in expectation
-- statement:
--   Any finite collection of true original stochastic stopping-time mesh cells in a compact C2 reserve band with uniformly small drift-centred Lévy increments has integrable signed absolute Taylor remainder, bounded by epsilon times its physical quadratic energy on the localisation event, including the final random clipped cell.
-- source:
--   Avram Palmowski Pistorius (2007) Proposition 4(i), original stopped Ito-Meyer compact-band Gaussian Taylor approximation; Proved uniform pre-left modulus and B27 random-stop energy.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_localise_original_preleft_compact_gaussian_finite_mesh_remainder
import Theorems.Thm_AvramDividend_Classical_avram_b27_original_random_stopped_compact_mesh_energy_L1
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b28_original_random_clipped_C2_taylor_L1_automatic
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbcap : ENNReal.ofReal b < C)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (A : Set Ω) (S : Finset ℕ)
        (s t : ℕ → Ω → ℝ≥0),
        let z : Ω → ℕ → ℝ := fun ω i =>
          Function.leftLim (fun u : ℝ≥0 =>
            x + X.X u ω - rightLimit D u ω) (s i ω)
        let g : Ω → ℕ → ℝ := fun ω i =>
          X.X (t i ω) ω - X.X (s i ω) ω -
            ((t i ω - s i ω) : ℝ) * X.c
        let Q : Ω → ℝ := fun ω => ∑ i ∈ S, (g ω i) ^ 2
        let R : Ω → ℝ := fun ω => ∑ i ∈ S,
          (w (z ω i + g ω i) -
            taylorWithinEval w 1 (Set.uIcc (z ω i) (z ω i + g ω i))
              (z ω i) (z ω i + g ω i) -
            (iteratedDeriv 2 w (z ω i) * (g ω i) ^ 2) / 2)
        (∀ i ∈ S, IsStoppingTime 𝓕.rightCont
          (fun ω => (s i ω : WithTop ℝ≥0))) →
        (∀ i ∈ S, IsStoppingTime 𝓕.rightCont
          (fun ω => (t i ω : WithTop ℝ≥0))) →
        (∀ᵐ ω ∂(P.restrict A), ∀ i ∈ S,
          z ω i ∈ Icc a b ∧ z ω i + g ω i ∈ Icc a b ∧
          z ω i ≠ z ω i + g ω i ∧
          dist (z ω i + g ω i) (z ω i) < δ) →
        AEStronglyMeasurable (fun ω => |R ω|) (P.restrict A) →
        IntegrableOn (fun ω => |R ω|) A P ∧
        (∫ ω in A, |R ω| ∂P) ≤
          ε * (∫ ω in A, Q ω ∂P) := by sorry
