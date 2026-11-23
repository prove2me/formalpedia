-- Prove2me | Theorems.Thm_DedekindZeta_Theta_summable_mixedGaussian_submodule
-- name    : DedekindZeta.Theta.summable_mixedGaussian_submodule
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:51:39.911985+00:00
-- url     : https://prove2.me/theorems/add3beef-b65f-436c-90ec-42ed11fe591a
-- title:
--   Theta: summable mixed Gaussian submodule
-- statement:
--   **Summability of the multiplicatively-scaled Gaussian over a fractional
--   ideal** (for a unit `y`, `mixedEmbedding.norm y ≠ 0`): the family
--   `a ↦ g(y · σ(a))` over `a ∈ J` is summable, being the Schwartz function
--   `mixedGaussianSchwartz K hy` restricted to the lattice `Λ(J)` and reindexed
--   through `idealLatticeEquiv`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L2218-L2235
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L2218-L2235

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section

theorem DedekindZeta.Theta.summable_mixedGaussian_submodule (J : FractionalIdeal (𝓞 K)⁰ K) (hJ : J ≠ 0)
    {y : mixedSpace K} (hy : mixedEmbedding.norm y ≠ 0) :
    Summable (fun a : (J : Submodule (𝓞 K) K) =>
      (mixedGaussian K (y * mixedEmbedding K (a : K)) : ℂ)) := by sorry
