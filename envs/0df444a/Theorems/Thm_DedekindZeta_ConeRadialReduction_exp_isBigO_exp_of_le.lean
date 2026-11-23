-- Prove2me | Theorems.Thm_DedekindZeta_ConeRadialReduction_exp_isBigO_exp_of_le
-- name    : DedekindZeta.ConeRadialReduction.exp_isBigO_exp_of_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:49:28.180087+00:00
-- url     : https://prove2.me/theorems/56533263-80a4-484c-96f9-a82720bedc4d
-- title:
--   Cone Radial Reduction: exp is Big O exp of le
-- statement:
--   **Comparison of Gaussian tails.** A faster Gaussian decay dominates a slower
--   one: if `0 < c ≤ c₁` and `α ≤ α₁` then `e^{-c₁ r^{α₁}} =O[atTop] e^{-c r^α}`
--   (for `r ≥ 1`, `c r^α ≤ c₁ r^{α₁}`). Used to unify the two decay rates of
--   `orbitTheta`/`orbitThetaFrac` into a single `(c, α)` pair.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L2323-L2339
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L2323-L2339

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

theorem DedekindZeta.ConeRadialReduction.exp_isBigO_exp_of_le {c₁ α₁ c α : ℝ} (hcpos : 0 < c) (hcle : c ≤ c₁)
    (hαle : α ≤ α₁) :
    (fun r : ℝ => Real.exp (-c₁ * r ^ α₁)) =O[Filter.atTop]
      (fun r : ℝ => Real.exp (-c * r ^ α)) := by sorry
