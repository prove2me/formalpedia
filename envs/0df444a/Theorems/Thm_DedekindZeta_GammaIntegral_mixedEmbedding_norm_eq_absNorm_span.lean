-- Prove2me | Theorems.Thm_DedekindZeta_GammaIntegral_mixedEmbedding_norm_eq_absNorm_span
-- name    : DedekindZeta.GammaIntegral.mixedEmbedding_norm_eq_absNorm_span
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:25:25.140852+00:00
-- url     : https://prove2.me/theorems/b7650b4b-136f-418a-9da2-2d3ee73e1b64
-- title:
--   Gamma Integral: mixed Embedding norm eq abs Norm span
-- statement:
--   **Norm identity** (the standard treatment): the archimedean norm of the Minkowski
--   embedding of `a : 𝓞 K` equals the absolute norm of the principal ideal `(a)`,
--   `|N(σ a)| = 𝔑((a))` (as nonnegative reals). Bridges
--   `mixedEmbedding.norm_eq_norm` (`= |Algebra.norm ℚ a|`) and
--   `Ideal.absNorm_span_singleton` (`= |Algebra.norm ℤ a|`).
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/GammaIntegral.lean#L1395-L1399
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/GammaIntegral.lean#L1395-L1399

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_GammaIntegral
set_option autoImplicit true
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory
open scoped Real ENNReal
open DedekindZeta DedekindZeta.GammaIntegral
open DedekindZeta DedekindZeta.Theta
open NumberField.Units NumberField.Units.dirichletUnitTheorem
attribute [local instance] DedekindZeta.coneMulAction DedekindZeta.coneMeasurableConstSMul
  DedekindZeta.coneCountable DedekindZeta.coneSMulInvariantMeasure
variable (K : Type*) [Field K] [NumberField K]
noncomputable section

theorem DedekindZeta.GammaIntegral.mixedEmbedding_norm_eq_absNorm_span (a : 𝓞 K) :
    mixedEmbedding.norm (mixedEmbedding K ((a : 𝓞 K) : K))
      = (Ideal.absNorm (Ideal.span {a}) : ℝ) := by sorry
