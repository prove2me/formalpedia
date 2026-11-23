-- Prove2me | Theorems.Thm_DedekindZeta_integrable_indicator_mixedThetaKernel_mul_norm_cpow
-- name    : DedekindZeta.integrable_indicator_mixedThetaKernel_mul_norm_cpow
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:25:41.024077+00:00
-- url     : https://prove2.me/theorems/24580a32-898f-401e-a3fd-49c7a344f0e0
-- title:
--   Dedekind Zeta: integrable indicator mixed Theta Kernel mul norm cpow
-- statement:
--   **Integrability of the fractional theta cone integrand** for `1 < t.re`.
--   For any fractional ideal `I` and
--   `t : ℂ` with `1 < t.re`, the fundamental-cone indicator of the integrand
--   `y ↦ Θ(I, y)·N(y)^t` is `mixedMulHaar`-integrable.
--
--   This is the genuine analytic convergence of the cone Mellin integral. The
--   fundamental cone meets every archimedean-norm shell `N(y) ∈ (0, ∞)`; near
--   `N(y) → 0` the theta kernel diverges like `N(y)⁻¹` (the pole side of the
--   inversion law `Theta.mixedThetaKernel_inv_*`), so the radial Mellin integral
--   `∫ N^{t-2} dN` converges exactly when `Re t > 1`. The estimate is the same one
--   underlying the sum/integral interchange in the *integral* representative case
--   (`GammaIntegral.cone_integral_idealThetaKernel_eq_tsum`, Tonelli for the
--   nonnegative Gaussian dominated by `summable_absNorm_neg_cpow`); since
--   `Theta.idealThetaKernel K 𝔞 = Theta.mixedThetaKernel K (𝔞 : FractionalIdeal)`
--   (`Theta.idealThetaKernel_eq_mixed`) the bound transfers to coerced integral
--   ideals and, more generally, to any fractional ideal's lattice.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Statements.lean#L2487-L2535
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Statements.lean#L2487-L2535

import Mathlib
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_Statements
set_option autoImplicit true
open NumberField NumberField.InfinitePlace IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open Filter Finset Asymptotics Topology
open scoped Real nonZeroDivisors
open DedekindZeta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
open scoped NNReal ENNReal

theorem DedekindZeta.integrable_indicator_mixedThetaKernel_mul_norm_cpow
    (I : FractionalIdeal (𝓞 K)⁰ K) (t : ℂ) (ht : 1 < t.re) :
    MeasureTheory.Integrable
      ((mixedEmbedding.fundamentalCone K).indicator
        (fun y => Theta.mixedThetaKernel K I y * (mixedEmbedding.norm y : ℂ) ^ t))
      (mixedMulHaar K) := by sorry
