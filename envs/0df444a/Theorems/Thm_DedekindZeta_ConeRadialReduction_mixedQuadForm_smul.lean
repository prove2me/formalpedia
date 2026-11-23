-- Prove2me | Theorems.Thm_DedekindZeta_ConeRadialReduction_mixedQuadForm_smul
-- name    : DedekindZeta.ConeRadialReduction.mixedQuadForm_smul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:48:44.8408+00:00
-- url     : https://prove2.me/theorems/262f167f-cb98-493f-bec0-6301f5b26044
-- title:
--   Cone Radial Reduction: mixed Quad Form smul
-- statement:
--   **Homogeneity of degree 2.** `Q(c • y) = c² · Q(y)`: each place norm scales
--   by `|c|` (`normAtPlace_smul`), so its square scales by `c²`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L1250-L1256
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L1250-L1256

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

theorem DedekindZeta.ConeRadialReduction.mixedQuadForm_smul (c : ℝ) (y : mixedSpace K) :
    mixedQuadForm K (c • y) = c ^ 2 * mixedQuadForm K y := by sorry
