-- Prove2me | Theorems.Thm_DedekindZeta_ConeRadialReduction_exists_mixedEmbedding_norm_lower_bound
-- name    : DedekindZeta.ConeRadialReduction.exists_mixedEmbedding_norm_lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:49:16.173453+00:00
-- url     : https://prove2.me/theorems/c19cc14b-6f3c-4331-beb4-ed94267c72e7
-- title:
--   Cone Radial Reduction: exists mixed Embedding norm lower bound
-- statement:
--   **Uniform lower bound on the absolute norm of nonzero ideal elements.**
--   For a nonzero fractional ideal `I` there is `m > 0` with
--   `m ≤ N(σ a) = |Algebra.norm ℚ a|` for *every* nonzero `a ∈ I`.  This is the
--   lattice analogue of "a nonzero algebraic integer has `|N| ≥ 1`": writing the
--   fractional ideal as `δ⁻¹ · (integral ideal)` (`IsFractional`, witness
--   `δ ∈ (𝓞 K)⁰`), `δ·a` is a nonzero algebraic integer, so `|N(δ a)| ≥ 1` and
--   `|N a| ≥ 1/|N δ| =: m`.  the standard treatment (the discrete-lattice positivity
--   underlying the spectral gap).
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L1868-L1918
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L1868-L1918

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

theorem DedekindZeta.ConeRadialReduction.exists_mixedEmbedding_norm_lower_bound (I : FractionalIdeal (𝓞 K)⁰ K)
    (hI : I ≠ 0) :
    ∃ m : ℝ, 0 < m ∧ ∀ a : K, a ∈ (I : Submodule (𝓞 K) K) → a ≠ 0 →
      m ≤ mixedEmbedding.norm (mixedEmbedding K a) := by sorry
