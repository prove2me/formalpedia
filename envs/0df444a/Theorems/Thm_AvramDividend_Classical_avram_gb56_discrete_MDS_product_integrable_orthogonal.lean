-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gb56_discrete_MDS_product_integrable_orthogonal
-- name    : AvramDividend.Classical.avram_gb56_discrete_MDS_product_integrable_orthogonal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T11:49:48.882672+00:00
-- url     : https://prove2.me/theorems/646926bc-774f-4aeb-82ac-eb6d057d31f7
-- title:
--   Discrete martingale differences in L2 have integrable orthogonal cross-products
-- statement:
--   For a finite measure and a discrete-time filtration, square-integrable martingale differences that are measurable at their successor times have integrable pair products and zero cross integral for strictly ordered indices. This combines the published Martingale orthogonality theorem with Mathlib's Holder integrability theorem.

import Mathlib
import Theorems.Thm_Martingale_integral_mul_mds_eq_zero
open MeasureTheory
open scoped ENNReal NNReal

theorem AvramDividend.Classical.avram_gb56_discrete_MDS_product_integrable_orthogonal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsFiniteMeasure P] (𝓖 : Filtration ℕ mΩ)
    (V : ℕ → Ω → ℝ)
    (hmem : ∀ j, MemLp (V j) 2 P)
    (hadapt : ∀ j, StronglyMeasurable[𝓖 (j + 1)] (V j))
    (hmds : ∀ j, P[V j | 𝓖 j] =ᵐ[P] 0)
    (i r : ℕ) (hir : i < r) :
    Integrable (fun ω => V i ω * V r ω) P ∧
      (∫ ω, V i ω * V r ω ∂P) = 0 := by
  sorry
