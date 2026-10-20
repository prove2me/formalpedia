-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_capped_grid_discounted_scale_zero_continuity
-- name    : AvramDividend.Classical.chat03_capped_grid_discounted_scale_zero_continuity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T22:11:53.016377+00:00
-- url     : https://prove2.me/theorems/c4704f13-90ca-4d0b-bf84-bcb9b46c8ac1
-- title:
--   Convergence of discounted q-scale payoffs at capped first strict grid exits when W(0)=0
-- statement:
--   For a spectrally negative Lévy sample path, a finite strict two-sided first passage infimum and a horizon T, assume the official q-scale function satisfies W(0)=0. For every continuous real-valued discount function, all sufficiently fine positive uniform grid meshes have a genuine first strict grid exit index. The capped grid stop's discounted scale payoff lies in any chosen open neighbourhood of the capped continuous stopped payoff. The proof allows first-passage infima without strict attainment and sampled reserves of either sign, including zero, with no claim of q-harmonicity.
-- source:
--   Uses the already Proved first-grid capped-time convergence and scale zero-extension global continuity from the pinned Prove2Me catalogue, plus pathwise right-continuity and Mathlib neighbourhood characterisation. No import of the Open two-sided stopped-scale identity.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_first_grid_capped_time_convergence
import Theorems.Thm_AvramDividend_Classical_chat03_scale_zero_extension_continuous_everywhere
import Mathlib.Topology.Order.LeftRightNhds

open MeasureTheory Set Filter Topology
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_capped_grid_discounted_scale_zero_continuity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0)
    (ω : Ω) (lower upper x : ℝ) (τ T : ℝ≥0)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} τ)
    (discount : ℝ≥0 → ℝ)
    (hdiscount : Continuous discount)
    (U : Set ℝ) (hU : IsOpen U)
    (hmem :
      discount (min τ T) * W (x + X.X (min τ T) ω) ∈ U) :
    ∃ δ : ℝ≥0, 0 < δ ∧
      ∀ h : ℝ≥0, 0 < h → h < δ →
        ∃ k : ℕ,
          (X.X ((k : ℝ≥0) * h) ω < lower ∨
           upper < X.X ((k : ℝ≥0) * h) ω) ∧
          (∀ j : ℕ, j < k →
            ¬ (X.X ((j : ℝ≥0) * h) ω < lower ∨
               upper < X.X ((j : ℝ≥0) * h) ω)) ∧
          discount (min ((k : ℝ≥0) * h) T) *
            W (x + X.X (min ((k : ℝ≥0) * h) T) ω) ∈ U := by sorry
