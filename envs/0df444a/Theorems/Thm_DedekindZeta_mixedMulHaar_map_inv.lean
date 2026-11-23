-- Prove2me | Theorems.Thm_DedekindZeta_mixedMulHaar_map_inv
-- name    : DedekindZeta.mixedMulHaar_map_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:25:30.847955+00:00
-- url     : https://prove2.me/theorems/8ef7d585-cf5b-4c67-a091-2fd50908ed2b
-- title:
--   Dedekind Zeta: mixed Mul Haar map inv
-- statement:
--   **Inversion-invariance of the multiplicative Haar measure** `d^*x`
--   (the standard treatment): the standard-normalised multiplicative Haar measure
--   `mixedMulHaar = (2/π)^{r₂}·|N(x)|^{-1}·dx` on `K_ℝ^*` is invariant under the
--   group inversion `x ↦ x⁻¹`. This is the measure-theoretic content of the Mellin
--   principle's change of variables: the density `|N(x)|^{-1}` is itself the
--   multiplicative Haar density, hence inversion-stable once paired with the
--   componentwise Jacobian.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/GammaIntegral.lean#L1051-L1169
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/GammaIntegral.lean#L1051-L1169

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_GammaIntegral
set_option autoImplicit true
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory
open scoped Real ENNReal
open DedekindZeta
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory
variable {K : Type*} [Field K] [NumberField K]
noncomputable section
set_option maxHeartbeats 1000000

theorem DedekindZeta.mixedMulHaar_map_inv :
    Measure.map (fun x : mixedEmbedding.mixedSpace K => x⁻¹) (mixedMulHaar K)
      = mixedMulHaar K := by sorry
