-- Prove2me | Theorems.Thm_DedekindZeta_ConeRadialReduction_lintegral_collar_weight
-- name    : DedekindZeta.ConeRadialReduction.lintegral_collar_weight
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:48:00.247069+00:00
-- url     : https://prove2.me/theorems/761c6216-b7ff-4b57-bf4c-9be3afa31818
-- title:
--   Cone Radial Reduction: lintegral collar weight
-- statement:
--   **Inner 1D radial weight integral** (step-5 helper for the collar
--   disintegration). For a fixed norm value `n`, the `t`-fiber of the collar
--   `{N ∈ (1, e]}` carries the multiplicative-Haar mass
--   `∫_{t : t < n ≤ e·t} dr/r = ∫_1^e dr/r = 1` when `n > 0`, and `0` when `n ≤ 0`
--   (then no `t > 0` can satisfy `t < n`). Concretely the membership
--   `n ∈ Ioc t (e·t)` is `t < n ∧ n ≤ e·t`, i.e. `t ∈ Ico (n/e) n`, and
--   `∫_{n/e}^{n} dt/t = log n - log (n/e) = log e = 1`. the standard treatment (radial
--   weight `dr/r`). Consumed by the collar disintegration assembly.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L235-L304
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L235-L304

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

theorem DedekindZeta.ConeRadialReduction.lintegral_collar_weight (n : ℝ) :
    ∫⁻ t in Set.Ioi (0 : ℝ),
        ENNReal.ofReal t⁻¹ * (Set.Ioc t (Real.exp 1 * t)).indicator (1 : ℝ → ℝ≥0∞) n
          ∂volume
      = if 0 < n then 1 else 0 := by sorry
