-- Prove2me | Theorems.Thm_DedekindZeta_integrable_real_gaussian_mul_abs_rpow
-- name    : DedekindZeta.integrable_real_gaussian_mul_abs_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:44:59.642554+00:00
-- url     : https://prove2.me/theorems/bcc5b152-acda-45aa-a768-ac2100163119
-- title:
--   Dedekind Zeta: integrable real gaussian mul abs rpow
-- statement:
--   **Real-place 1D integrability helper** (the standard treatment). The per-real-place
--   integrand obtained after absorbing the `dx/|x|` density of `mixedMulHaar`, namely
--   `x ↦ e^{-π x²} |x|^{σ-1}`, is `volume`-integrable on `ℝ` when `0 < σ`. Established
--   here at the `Statements` layer (rather than cited from the downstream
--   `GammaIntegral`, which imports this file) to feed the whole-space convergence
--   lemma below. Mirrors `integrable_rpow_mul_exp_neg_mul_sq`, using evenness and
--   `integrableOn_rpow_mul_exp_neg_mul_sq` on `Set.Ioi 0`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Statements.lean#L1621-L1644
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Statements.lean#L1621-L1644

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

theorem DedekindZeta.integrable_real_gaussian_mul_abs_rpow {σ : ℝ} (hσ : 0 < σ) :
    MeasureTheory.Integrable
      (fun x : ℝ => Real.exp (-Real.pi * x ^ 2) * |x| ^ (σ - 1)) := by sorry
