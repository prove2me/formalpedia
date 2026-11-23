-- Prove2me | Theorems.Thm_DedekindZeta_Theta_mixedThetaKernel_inversion
-- name    : DedekindZeta.Theta.mixedThetaKernel_inversion
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:21:39.188968+00:00
-- url     : https://prove2.me/theorems/b18a2c6c-1d25-498a-8e8e-7caaa13571a5
-- title:
--   Theta: mixed Theta Kernel inversion
-- statement:
--   **Kernel inversion law via Poisson summation** (the standard treatment at
--   the multiplicative lattice level): for a nonzero integral ideal `𝔞` and a unit
--   `x ∈ K_ℝ^*` (`N(x) ≠ 0`),
--
--       Θ(𝔞, x⁻¹) = (|N(x)| / vol(Λ(𝔞))) · (Θ((𝔞𝔡)⁻¹, x) + 1) - 1,
--
--   where `vol(Λ(𝔞)) = covolume K 𝔞` and `(𝔞𝔡)⁻¹ = dualIdeal K 𝔞`.  The proof
--   applies lattice Poisson summation to the Schwartz Gaussian
--   `mixedGaussianSchwartz K hxinv` over `Λ(𝔞)`: the primal whole-lattice sum is
--   `1 + Θ(𝔞, x⁻¹)` (`tsum_mixedGaussian_submodule`), and the Fourier side, via
--   `fourier_mixedGaussian_scaling` (Jacobian `|N(x)|`) and the conjugation-twisted
--   dual lattice `dualLattice_idealLattice` (the twist is absorbed by
--   `mixedGaussian_mul_conjMixed`), is `|N(x)| · (1 + Θ((𝔞𝔡)⁻¹, x))`; the covolume
--   constant is `covolume_idealLattice`.  The `+1`/`-1` correction is the
--   asymmetric `g(0) = 1` term and is essential (the clean form is false).
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L2295-L2399
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L2295-L2399

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section

theorem DedekindZeta.Theta.mixedThetaKernel_inversion (𝔞 : Ideal (𝓞 K)) (hne : 𝔞 ≠ 0)
    (x : mixedEmbedding.mixedSpace K) (hx : mixedEmbedding.norm x ≠ 0) :
    mixedThetaKernel K (𝔞 : FractionalIdeal (𝓞 K)⁰ K) x⁻¹ =
      ((|mixedEmbedding.norm x| / covolume K 𝔞 : ℝ) : ℂ) *
        (mixedThetaKernel K (dualIdeal K 𝔞) x + 1) - 1 := by sorry
