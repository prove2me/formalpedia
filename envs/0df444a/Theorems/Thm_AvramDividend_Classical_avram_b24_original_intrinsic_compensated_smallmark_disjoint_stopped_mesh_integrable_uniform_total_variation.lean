-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_original_intrinsic_compensated_smallmark_disjoint_stopped_mesh_integrable_uniform_total_variation
-- name    : AvramDividend.Classical.avram_b24_original_intrinsic_compensated_smallmark_disjoint_stopped_mesh_integrable_uniform_total_variation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T19:40:11.826732+00:00
-- url     : https://prove2.me/theorems/5bf6faab-dd10-4fff-96f1-f9b153e2e9fc
-- title:
--   True original finite-activity compensated smallmark total variation on ANY disjoint stopped physical grid has one integrable Poisson-count envelope independent of refinement
-- statement:
--   For the original nonzero-jump spectrally negative finite-activity Lévy X on Ω/P and any same-source intrinsic compensated Jsmall residual witness, a SINGLE integrable true original smallnegative marked Poisson jump count plus full signed smallmark drift envelope B_T dominates the TOTAL ABSOLUTE Jsmall variation across EVERY finite system of pairwise disjoint actual half-open physical cells (a_i,b_i] within [0,T] whose total physical length does not exceed T, simultaneously on one P-conull event. This bound holds uniformly across all actual refining stopped physical partitions, regardless of the number of cells, retaining a negative terminal ruin-causing mark in the unique last right-inclusive cell. It combines proved true finite source interval variation, exact original smallnegative Poisson count/card identification, disjoint finite marked support counting and the integrable uniform original smallmark count envelope. Crucially this supplies the actual L1 common-refinement total variation budget needed by B219 marked predictable-coefficient perturbations without moment assumptions on large negative jumps, Brownian ν=0 sources or postruin continuation.
-- source:
--   B24 proved original true smallmark interval variation and marked count/card, disjoint physical mark count and genuine integrable smallmark Poisson envelope.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_original_intrinsic_compensated_smallmark_disjoint_stopped_mesh_integrable_uniform_total_variation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (Jsmall : ℝ≥0 → Ω → ℝ)
    (hJsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω)
        atTop (𝓝 (Jsmall t ω)))
    (T : ℝ≥0) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Ioo (-1 : ℝ) 0)
    let B : Ω → ℝ := fun ω => (N ω).toReal +
      (T : ℝ) * ‖∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν‖
    Integrable B P ∧
      ∀ᵐ ω ∂P, ∀ (I : Finset ℕ) (a b : ℕ → ℝ≥0),
        (∀ i ∈ I, a i ≤ b i ∧ b i ≤ T) →
        (∀ i ∈ I, ∀ j ∈ I, i ≠ j →
          Disjoint (Ioc (a i) (b i)) (Ioc (a j) (b j))) →
        (∑ i ∈ I, ((b i : ℝ) - (a i : ℝ))) ≤ (T : ℝ) →
        (∑ i ∈ I, ‖Jsmall (b i) ω - Jsmall (a i) ω‖) ≤ B ω := by sorry
