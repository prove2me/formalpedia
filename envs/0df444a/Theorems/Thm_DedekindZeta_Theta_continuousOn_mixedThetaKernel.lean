-- Prove2me | Theorems.Thm_DedekindZeta_Theta_continuousOn_mixedThetaKernel
-- name    : DedekindZeta.Theta.continuousOn_mixedThetaKernel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:52:05.545243+00:00
-- url     : https://prove2.me/theorems/a5ddd810-ca12-4789-8016-3c4c10cc81a2
-- title:
--   Theta: continuous On mixed Theta Kernel
-- statement:
--   **Continuity of the fractional theta kernel** `x ↦ mixedThetaKernel K I x` on
--   the open nonzero-norm locus `{x | N(x) ≠ 0}` (the exact Gaussian-convergence
--   region: on the zero-norm locus the lattice family is non-summable).
--
--   The kernel is the lattice sum `∑'_{a} g(x · σ(a))` of the (continuous) Minkowski
--   Gaussian over the nonzero elements of `I`.  Working locally at a point `x₀` with
--   `N(x₀) ≠ 0`: a closed ball `B ⊆ {N ≠ 0}` is compact, so each `normAtPlace w` is
--   bounded below by some `δ > 0` on `B`; multiplicativity gives, for `x ∈ B`,
--   `∑_w mult w · normAtPlace w (x·σ(a))² ≥ δ²‖eEmb a‖²`, hence each summand is
--   dominated by `exp(-π δ²‖eEmb a‖²)`, which is summable (`summable_theta`).
--   `continuousOn_tsum` then gives continuity on `B`, hence `ContinuousAt x₀`
--   (the standard treatment).
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L1066-L1166
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L1066-L1166

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section

theorem DedekindZeta.Theta.continuousOn_mixedThetaKernel (I : FractionalIdeal (𝓞 K)⁰ K) :
    ContinuousOn (mixedThetaKernel K I)
      {x : mixedEmbedding.mixedSpace K | mixedEmbedding.norm x ≠ 0} := by sorry
