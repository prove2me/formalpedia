-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b30_original_random_mesh_taylor_mean_vanish_of_uniform_energy
-- name    : AvramDividend.Classical.avram_b30_original_random_mesh_taylor_mean_vanish_of_uniform_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T00:03:51.772387+00:00
-- url     : https://prove2.me/theorems/875e787a-fa16-482a-b975-c1c457f09771
-- title:
--   Original random stopped C2 Taylor expected errors vanish under uniform physical source energy
-- statement:
--   On any physical original-source localisation event whose random stopped mesh remains inside a C2 reserve band, has asymptotically small actual source displacements and uniformly bounded expected quadratic energy, the expected absolute original Taylor remainder converges to zero. The random final stopped cell is included whenever it stays in the band.
-- source:
--   Avram Palmowski Pistorius (2007) Proposition 4(i), original stopped Ito-Meyer mesh convergence; B28 random stopped C2 Taylor L1 estimate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_b28_original_random_clipped_C2_taylor_L1_automatic
open MeasureTheory Set Filter Metric Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b30_original_random_mesh_taylor_mean_vanish_of_uniform_energy
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
      let Q : ℕ → Ω → ℝ := fun m ω =>
        ∑ i ∈ S m, (g m ω i) ^ 2
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
      (∃ K : ℝ, 0 ≤ K ∧ ∀ m, (∫ ω in A, Q m ω ∂P) ≤ K) →
      Tendsto (fun m => ∫ ω in A, |R m ω| ∂P)
        atTop (𝓝 (0 : ℝ)) := by sorry
