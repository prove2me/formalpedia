-- Prove2me | Theorems.Thm_DedekindZeta_PoissonSummation_summable_periodisation_fourier
-- name    : DedekindZeta.PoissonSummation.summable_periodisation_fourier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:48:59.614546+00:00
-- url     : https://prove2.me/theorems/b36d3965-8f93-44a8-bc5f-2dd538168604
-- title:
--   Poisson Summation: summable periodisation fourier
-- statement:
--   **Absolute convergence of the dual Fourier series.** For every `x`, the
--   character-weighted family of Fourier coefficients
--   `w ↦ 𝐞(⟪x,w⟫) • (vol L)⁻¹ · 𝓕 f w` is summable over `dualLattice L`. The
--   coefficients decay rapidly because `𝓕 f` is again Schwartz
--   (`SchwartzMap.fourierTransformCLM`); the character has modulus one, so it does
--   not affect summability. Reuse the
--   `ZLattice.summable_norm_sub_rpow` + `summable_of_isBigO` pattern of
--   `summable_periodisation`, transported to the dual lattice.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/PoissonSummation.lean#L462-L499
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/PoissonSummation.lean#L462-L499

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
set_option autoImplicit true
open MeasureTheory Module
open scoped FourierTransform RealInnerProductSpace
open DedekindZeta DedekindZeta.PoissonSummation
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
  (f : SchwartzMap V ℂ)

theorem DedekindZeta.PoissonSummation.summable_periodisation_fourier (x : V) :
    Summable (fun w : dualLattice L =>
      𝐞 (⟪x, (w : V)⟫) •
        ((ZLattice.covolume L : ℂ)⁻¹ * 𝓕 (f : V → ℂ) (w : V))) := by sorry
