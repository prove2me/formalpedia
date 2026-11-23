-- Prove2me | Theorems.Thm_DedekindZeta_ae_norm_ne_zero
-- name    : DedekindZeta.ae_norm_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:23:54.608893+00:00
-- url     : https://prove2.me/theorems/f4fea63c-aae3-4732-8638-6eed96d8ee3a
-- title:
--   Dedekind Zeta: ae norm ne zero
-- statement:
--   The norm-vanishing locus is `mixedMulHaar`-null: the density of `mixedMulHaar`
--   vanishes where `mixedEmbedding.norm = 0`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Statements.lean#L1153-L1166
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Statements.lean#L1153-L1166

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

theorem DedekindZeta.ae_norm_ne_zero :
    ∀ᵐ x ∂(mixedMulHaar K), mixedEmbedding.norm x ≠ 0 := by sorry
