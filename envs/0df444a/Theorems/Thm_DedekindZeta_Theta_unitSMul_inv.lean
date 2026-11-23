-- Prove2me | Theorems.Thm_DedekindZeta_Theta_unitSMul_inv
-- name    : DedekindZeta.Theta.unitSMul_inv
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:16:42.679133+00:00
-- url     : https://prove2.me/theorems/0e5ce12e-a744-455c-862d-694151e521ca
-- title:
--   Theta: unit SMul inv
-- statement:
--   The `unitSMul` action commutes with the mixed-space inverse:
--   `(u • x)⁻¹ = u⁻¹ • x⁻¹`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L1267-L1274
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L1267-L1274

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section

theorem DedekindZeta.Theta.unitSMul_inv (u : (𝓞 K)ˣ) (x : mixedEmbedding.mixedSpace K) :
    (u • x)⁻¹ = u⁻¹ • x⁻¹ := by sorry
