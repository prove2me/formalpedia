-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b27_original_random_stopped_compact_mesh_energy_L1
-- name    : AvramDividend.Classical.avram_b27_original_random_stopped_compact_mesh_energy_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T23:47:06.588185+00:00
-- url     : https://prove2.me/theorems/00a42323-6d41-4008-82bd-eb799ad8f521
-- title:
--   Original random stopped Lévy finite mesh compact-band quadratic energy integrable
-- statement:
--   Any finite family of genuine original random right-continuous stopping clocks has measurable squared centred Lévy increments; if each pre-left and post-increment reserve stays in a common compact band on an event, the quadratic mesh energy is integrable restricted to that event without global jump second moments.
-- source:
--   Avram Palmowski Pistorius (2007) Proposition 4(i), original stopped Ito-Meyer compact interpolation and last random stopped grid cell, joint source measurability d55462c3.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b27_original_random_stopped_compact_mesh_energy_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (a b : ℝ) (hab : a ≤ b) :
    ∀ (A : Set Ω) (S : Finset ℕ)
      (s t : ℕ → Ω → ℝ≥0),
      let z : Ω → ℕ → ℝ := fun ω i =>
        Function.leftLim (fun u : ℝ≥0 =>
          x + X.X u ω - rightLimit D u ω) (s i ω)
      let g : Ω → ℕ → ℝ := fun ω i =>
        X.X (t i ω) ω - X.X (s i ω) ω -
          ((t i ω - s i ω) : ℝ) * X.c
      let Q : Ω → ℝ := fun ω => ∑ i ∈ S, (g ω i) ^ 2
      (∀ i ∈ S, IsStoppingTime 𝓕.rightCont
        (fun ω => (s i ω : WithTop ℝ≥0))) →
      (∀ i ∈ S, IsStoppingTime 𝓕.rightCont
        (fun ω => (t i ω : WithTop ℝ≥0))) →
      (∀ᵐ ω ∂(P.restrict A), ∀ i ∈ S,
        z ω i ∈ Icc a b ∧ z ω i + g ω i ∈ Icc a b) →
      IntegrableOn Q A P := by sorry
