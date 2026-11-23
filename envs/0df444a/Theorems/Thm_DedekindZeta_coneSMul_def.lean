-- Prove2me | Theorems.Thm_DedekindZeta_coneSMul_def
-- name    : DedekindZeta.coneSMul_def
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:23:57.503677+00:00
-- url     : https://prove2.me/theorems/69e77444-fdf5-45ed-b7f0-3241b42d8a98
-- title:
--   Dedekind Zeta: cone SMul def
-- statement:
--   Unfolding of the cone action: `g • x = coneUnitHom g • x`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Statements.lean#L1097-L1099
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Statements.lean#L1097-L1099

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
variable {K}

theorem DedekindZeta.coneSMul_def (g : Multiplicative (Fin (NumberField.Units.rank K) → ℤ))
    (x : mixedEmbedding.mixedSpace K) :
    g • x = (coneUnitHom (K := K) g) • x := by sorry
