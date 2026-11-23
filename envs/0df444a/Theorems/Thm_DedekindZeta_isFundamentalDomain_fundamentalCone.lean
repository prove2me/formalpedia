-- Prove2me | Theorems.Thm_DedekindZeta_isFundamentalDomain_fundamentalCone
-- name    : DedekindZeta.isFundamentalDomain_fundamentalCone
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:23:58.691794+00:00
-- url     : https://prove2.me/theorems/c4d9d6b3-73f3-429d-a979-abd4c95b190f
-- title:
--   Dedekind Zeta: is Fundamental Domain fundamental Cone
-- statement:
--   **The fundamental cone is a fundamental domain (modulo torsion).**
--   `mixedEmbedding.fundamentalCone K` is a `MeasureTheory.IsFundamentalDomain` for
--   the action of `Multiplicative (Fin (NumberField.Units.rank K) → ℤ)` (the free complement of
--   `torsion K`, acting via `coneUnitHom` and the unit action) on the mixed space
--   w.r.t. `mixedMulHaar K`. The three predicates are:
--   * measurability — `measurableSet_fundamentalCone`;
--   * a.e.-cover — `ae_norm_ne_zero` reduces to the norm-nonzero locus, where
--     `fundamentalCone.exists_unit_smul_mem` plus the torsion decomposition
--     (`exist_unique_eq_mul_prod`) provides a translate landing in the cone;
--   * a.e.-disjointness — for `g ≠ 1` the translates `g • cone` and `cone` are
--     genuinely disjoint, since two cone elements differing by `coneUnitHom g` would
--     force `coneUnitHom g ∈ torsion K` (`fundamentalCone.unit_smul_mem_iff_mem_torsion`),
--     i.e. `g = 1` (`coneUnitHom_mem_torsion_iff`).
--   Measure-invariance of the action is `measurePreserving_unitSMul`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Statements.lean#L1183-L1218
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Statements.lean#L1183-L1218

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
open MeasureTheory NumberField.mixedEmbedding
open NumberField.Units NumberField.Units.dirichletUnitTheorem
attribute [local instance] DedekindZeta.coneMulAction
attribute [local instance] DedekindZeta.coneMeasurableConstSMul
attribute [local instance] DedekindZeta.coneCountable
attribute [local instance] DedekindZeta.coneSMulInvariantMeasure
variable {K}

theorem DedekindZeta.isFundamentalDomain_fundamentalCone :
    IsFundamentalDomain (Multiplicative (Fin (NumberField.Units.rank K) → ℤ))
      (mixedEmbedding.fundamentalCone K) (mixedMulHaar K) := by sorry
