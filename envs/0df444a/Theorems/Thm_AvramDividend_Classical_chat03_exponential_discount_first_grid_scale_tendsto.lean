-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_exponential_discount_first_grid_scale_tendsto
-- name    : AvramDividend.Classical.chat03_exponential_discount_first_grid_scale_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T14:04:33.673631+00:00
-- url     : https://prove2.me/theorems/f7f65f83-e599-4fd4-960c-b6bbd88653d8
-- title:
--   Exponential-discounted q-scale convergence at genuine first grid crossings
-- statement:
--   The actual exponentially discounted q-scale reward at capped first strict uniform-grid crossings converges to its continuous capped passage reward whenever W(0)=0, the positive mesh tends to zero, and the selected indices are eventually genuine first crossings. This exact q-discounted form interfaces with the finite-horizon expectation convergence theorem.
-- source:
--   Specialisation of Proved Chat03 sequential stopped-scale convergence using continuity of the NNReal-to-real coercion, multiplication by q, negation and real exponential.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_capped_grid_discounted_scale_mesh_tendsto
import Mathlib.Topology.Instances.ENNReal.Lemmas

open MeasureTheory Set Filter Topology
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_exponential_discount_first_grid_scale_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0)
    (ω : Ω) (lower upper x : ℝ) (τ T : ℝ≥0)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} τ)
    (mesh : ℕ → ℝ≥0)
    (hmesh : Tendsto mesh atTop (𝓝 0))
    (hpos : ∀ n, 0 < mesh n)
    (first : ℕ → ℕ)
    (hfirst : ∀ᶠ n in atTop,
      (X.X ((first n : ℝ≥0) * mesh n) ω < lower ∨
       upper < X.X ((first n : ℝ≥0) * mesh n) ω) ∧
      (∀ j : ℕ, j < first n →
        ¬ (X.X ((j : ℝ≥0) * mesh n) ω < lower ∨
           upper < X.X ((j : ℝ≥0) * mesh n) ω))) :
    Tendsto (fun n =>
      Real.exp (-(q * ((min ((first n : ℝ≥0) * mesh n) T) : ℝ))) *
        W (x + X.X (min ((first n : ℝ≥0) * mesh n) T) ω))
      atTop
      (𝓝 (Real.exp (-(q * ((min τ T) : ℝ))) *
        W (x + X.X (min τ T) ω))) := by sorry
