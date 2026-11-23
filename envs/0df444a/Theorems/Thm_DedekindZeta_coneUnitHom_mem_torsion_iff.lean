-- Prove2me | Theorems.Thm_DedekindZeta_coneUnitHom_mem_torsion_iff
-- name    : DedekindZeta.coneUnitHom_mem_torsion_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:24:07.944809+00:00
-- url     : https://prove2.me/theorems/eccd86b2-b843-43cd-886f-2daaae9a499b
-- title:
--   Dedekind Zeta: cone Unit Hom mem torsion iff
-- statement:
--   `coneUnitHom g` is a root of unity (torsion) iff `g` is trivial: the image of
--   `coneUnitHom` meets `torsion K` only in the identity, i.e. `coneUnitHom` realises
--   a complement of `torsion K`. Proved from the uniqueness in Dirichlet's unit
--   theorem (`exist_unique_eq_mul_prod`).
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Statements.lean#L1130-L1148
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Statements.lean#L1130-L1148

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

theorem DedekindZeta.coneUnitHom_mem_torsion_iff (g : Multiplicative (Fin (NumberField.Units.rank K) → ℤ)) :
    (coneUnitHom (K := K) g : (𝓞 K)ˣ) ∈ torsion K ↔ g = 1 := by sorry
