-- Prove2me | Theorems.Thm_DedekindZeta_integrable_complexPlace_gaussian_rpow
-- name    : DedekindZeta.integrable_complexPlace_gaussian_rpow
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:45:08.526906+00:00
-- url     : https://prove2.me/theorems/66ffb258-c9d2-48bb-ae00-ec45d135ea7b
-- title:
--   Dedekind Zeta: integrable complex Place gaussian rpow
-- statement:
--   **Per-complex-place 1D integrability helper** (the standard treatment). After absorbing
--   the `(2/π) dλ/|z|²` density of `mixedMulHaar` at a complex place, the per-place
--   integrand is `e^{-2π‖z‖²}·‖z‖^{2(σ-1)}`, `volume`-integrable on `ℂ` exactly when
--   `0 < σ`. Established here at the `Statements` layer. Proof by polar coordinates,
--   reducing to a radial integral via `integrableOn_rpow_mul_exp_neg_mul_sq`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Statements.lean#L1652-L1702
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Statements.lean#L1652-L1702

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
open Set

theorem DedekindZeta.integrable_complexPlace_gaussian_rpow {σ : ℝ} (hσ : 0 < σ) :
    MeasureTheory.Integrable
      (fun z : ℂ => Real.exp (-2 * Real.pi * ‖z‖ ^ 2) * ‖z‖ ^ (2 * (σ - 1))) volume := by sorry
