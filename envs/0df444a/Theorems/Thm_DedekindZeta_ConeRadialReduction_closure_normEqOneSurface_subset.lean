-- Prove2me | Theorems.Thm_DedekindZeta_ConeRadialReduction_closure_normEqOneSurface_subset
-- name    : DedekindZeta.ConeRadialReduction.closure_normEqOneSurface_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:49:02.925313+00:00
-- url     : https://prove2.me/theorems/29acdd07-5db0-4f1b-ab67-e4a4dad3931c
-- title:
--   Cone Radial Reduction: closure norm Eq One Surface subset
-- statement:
--   **The closure of the norm-1 surface lies in the norm-1 locus.**
--   `mixedEmbedding.norm` is continuous and `{x | N x = 1}` is closed, while
--   `normEqOneSurface K ⊆ {N = 1}` (`mem_normEqOneSurface`), so the closure stays
--   inside.  In particular every point of the closure has nonzero norm.  This is the
--   geometric input letting `radialMap K r` push the (relatively compact) surface
--   slice into the Gaussian-summable nonzero-norm locus.  the standard treatment.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L1589-L1594
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L1589-L1594

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_GammaIntegral
import Definitions.Def_DedekindZeta_ConeRadialReduction
set_option autoImplicit true
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory Module
open scoped Real ENNReal nonZeroDivisors
open DedekindZeta DedekindZeta.ConeRadialReduction
variable (K : Type*) [Field K] [NumberField K]
variable {K}
variable (K)

theorem DedekindZeta.ConeRadialReduction.closure_normEqOneSurface_subset :
    closure (normEqOneSurface K) ⊆ {x : mixedSpace K | mixedEmbedding.norm x = 1} := by sorry
