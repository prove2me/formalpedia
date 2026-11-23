-- Prove2me | Theorems.Thm_DedekindZeta_Theta_idealThetaKernel_eq_mixed
-- name    : DedekindZeta.Theta.idealThetaKernel_eq_mixed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:51:17.475938+00:00
-- url     : https://prove2.me/theorems/e01fb8e1-8384-42a2-a433-a47521722b9c
-- title:
--   Theta: ideal Theta Kernel eq mixed
-- statement:
--   The integral kernel of `𝔞` is the fractional kernel of `(𝔞 : FractionalIdeal)`:
--   the two index sets `{a : 𝓞 K // a ∈ 𝔞 ∧ a ≠ 0}` and
--   `{a : K // a ∈ (𝔞 : FractionalIdeal) ∧ a ≠ 0}` are in canonical bijection via
--   the embedding `𝓞 K ↪ K`, and the summands agree. This bridges the integral
--   kernel used by `completedPartialZeta` to the fractional kernel in which the
--   inversion law is most naturally stated.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L965-L999
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L965-L999

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section

theorem DedekindZeta.Theta.idealThetaKernel_eq_mixed (𝔞 : Ideal (𝓞 K))
    (x : mixedEmbedding.mixedSpace K) :
    idealThetaKernel K 𝔞 x = mixedThetaKernel K (𝔞 : FractionalIdeal (𝓞 K)⁰ K) x := by sorry
