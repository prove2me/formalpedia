-- Prove2me | Theorems.Thm_DedekindZeta_Theta_idealThetaKernel_inversion
-- name    : DedekindZeta.Theta.idealThetaKernel_inversion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:21:45.223292+00:00
-- url     : https://prove2.me/theorems/2874e660-fff2-4c97-8735-0243cbfbf106
-- title:
--   Theta: ideal Theta Kernel inversion
-- statement:
--   **Inversion law for the integral kernel** (the exact form consumed by the
--   Mellin step): for a nonzero integral ideal `𝔞` and
--   `x ∈ K_ℝ^*`,
--
--       idealThetaKernel K 𝔞 x⁻¹
--         = (|N(x)| / vol(Λ(𝔞))) · (mixedThetaKernel K ((𝔞𝔡)⁻¹) x + 1) - 1.
--
--   Proved by rewriting the integral kernel as the fractional kernel
--   (`idealThetaKernel_eq_mixed`) and applying `mixedThetaKernel_inversion`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L2410-L2416
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L2410-L2416

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section

theorem DedekindZeta.Theta.idealThetaKernel_inversion (𝔞 : Ideal (𝓞 K)) (hne : 𝔞 ≠ 0)
    (x : mixedEmbedding.mixedSpace K) (hx : mixedEmbedding.norm x ≠ 0) :
    idealThetaKernel K 𝔞 x⁻¹ =
      ((|mixedEmbedding.norm x| / covolume K 𝔞 : ℝ) : ℂ) *
        (mixedThetaKernel K (dualIdeal K 𝔞) x + 1) - 1 := by sorry
