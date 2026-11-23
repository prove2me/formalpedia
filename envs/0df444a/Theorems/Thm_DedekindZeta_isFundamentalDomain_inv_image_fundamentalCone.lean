-- Prove2me | Theorems.Thm_DedekindZeta_isFundamentalDomain_inv_image_fundamentalCone
-- name    : DedekindZeta.isFundamentalDomain_inv_image_fundamentalCone
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:47:18.43081+00:00
-- url     : https://prove2.me/theorems/d6e6c104-44e9-4b12-9b31-6b2085bbe4f7
-- title:
--   Dedekind Zeta: is Fundamental Domain inv image fundamental Cone
-- statement:
--   **Inverse image of the fundamental cone is again a fundamental domain**
--   The set `(·⁻¹) '' fundamentalCone K` is a
--   `MeasureTheory.IsFundamentalDomain` for the *same* acting group
--   `Multiplicative (Fin (rank K) → ℤ)` (via `coneUnitHom` and the unit action) and
--   the *same* measure `mixedMulHaar K` as the cone itself
--   (`isFundamentalDomain_fundamentalCone`).  Proof: inversion `x ↦ x⁻¹` is an
--   involutive measure-preserving equivalence of the mixed space
--   (`measurable_mixedSpace_inv`, `mixedMulHaar_map_inv`) which intertwines the
--   action along the group inversion `g ↦ g⁻¹` of
--   `Multiplicative (Fin (rank K) → ℤ)`, since
--   `(g • x)⁻¹ = g⁻¹ • x⁻¹` (from `unitSMul_inv` through `coneUnitHom`).  Hence
--   `IsFundamentalDomain.image_of_equiv` transports the cone's fundamental-domain
--   property across inversion.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/GammaIntegral.lean#L1248-L1263
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/GammaIntegral.lean#L1248-L1263

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
open NumberField.Units NumberField.Units.dirichletUnitTheorem
attribute [local instance] DedekindZeta.coneMulAction DedekindZeta.coneMeasurableConstSMul
  DedekindZeta.coneCountable DedekindZeta.coneSMulInvariantMeasure

theorem DedekindZeta.isFundamentalDomain_inv_image_fundamentalCone :
    IsFundamentalDomain (Multiplicative (Fin (rank K) → ℤ))
      ((fun y : mixedEmbedding.mixedSpace K => y⁻¹) ''
        mixedEmbedding.fundamentalCone K) (mixedMulHaar K) := by sorry
