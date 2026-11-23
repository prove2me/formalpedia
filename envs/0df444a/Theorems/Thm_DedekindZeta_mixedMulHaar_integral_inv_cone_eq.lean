-- Prove2me | Theorems.Thm_DedekindZeta_mixedMulHaar_integral_inv_cone_eq
-- name    : DedekindZeta.mixedMulHaar_integral_inv_cone_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:47:12.776421+00:00
-- url     : https://prove2.me/theorems/4f2e87d1-5c4d-40b8-86be-ce0f989d1278
-- title:
--   Dedekind Zeta: mixed Mul Haar integral inv cone eq
-- statement:
--   **Inverse-cone change of domain**: for an `(𝓞 K)ˣ`-invariant
--   integrand `h` (`h (u • x) = h x`, the action being `mixedEmbedding.unitSMul`), the
--   `mixedMulHaar`-integral of `h` over the inverse cone `(·⁻¹) '' fundamentalCone K`
--   equals its integral over `fundamentalCone K`.
--
--   Both `fundamentalCone K` and its inverse image are fundamental domains for the
--   action of `(𝓞 K)ˣ` (modulo torsion) on the norm-nonzero locus of `K_ℝ` — the
--   inverse image because `x ↦ x⁻¹` commutes with the unit action
--   (`(u • x)⁻¹ = u⁻¹ • x⁻¹`, `unitSMul_inv`) and is `mixedMulHaar`-measure-preserving
--   (`mixedMulHaar_map_inv`). Hence the integral of a unit-invariant `h` over either
--   fundamental domain agrees (Mathlib `IsFundamentalDomain.setIntegral_eq`).
--
--   This is the change-of-domain identity consumed to pass
--   from the whole-space inversion substitution (`mulHaar_mellin_inv`) to the
--   fundamental-cone Mellin inversion identity. The genuine measure-theoretic
--   infrastructure it rests on — assembling the `IsFundamentalDomain` instance for
--   `fundamentalCone K` w.r.t. `mixedMulHaar K` and the measure-preserving unit
--   action — is established elsewhere in this development.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/GammaIntegral.lean#L1283-L1322
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/GammaIntegral.lean#L1283-L1322

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

theorem DedekindZeta.mixedMulHaar_integral_inv_cone_eq
    (h : mixedEmbedding.mixedSpace K → ℂ)
    (hinv : ∀ (u : (𝓞 K)ˣ) (x : mixedEmbedding.mixedSpace K), h (u • x) = h x)
    (hmeas : AEStronglyMeasurable h (mixedMulHaar K))
    (hint : Integrable
      ((mixedEmbedding.fundamentalCone K).indicator h) (mixedMulHaar K)) :
    ∫ x, ((fun y => y⁻¹) '' mixedEmbedding.fundamentalCone K).indicator h x
          ∂(mixedMulHaar K)
      = ∫ x, (mixedEmbedding.fundamentalCone K).indicator h x ∂(mixedMulHaar K) := by sorry
