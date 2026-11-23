-- Prove2me | Theorems.Thm_DedekindZeta_Theta_coe_unit_inv
-- name    : DedekindZeta.Theta.coe_unit_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:16:25.769934+00:00
-- url     : https://prove2.me/theorems/0e187ec5-6071-405a-9630-4f2d76708e24
-- title:
--   Theta: coe unit inv
-- statement:
--   The coercion `(↑u : K)` of a unit `u : (𝓞 K)ˣ` is invertible in `K`, with
--   inverse the coercion of `u⁻¹`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L1259-L1263
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L1259-L1263

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section

theorem DedekindZeta.Theta.coe_unit_inv (u : (𝓞 K)ˣ) :
    ((u : 𝓞 K) : K)⁻¹ = (((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) := by sorry
