-- Prove2me | solution 1 for mem_resolventSet_of_notMem_ball_of_spectrum_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:05:40.370895+00:00
-- url     : https://prove2.me/submissions/c10f58da-d0af-49bf-a680-77edd2928208

import Mathlib.Analysis.Complex.CauchyIntegral
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Definitions.Def_Operator_Crouzeix_CircleSymmetrized
import Definitions.Def_Operator_Crouzeix_AffinePolynomial
import Definitions.Def_Operator_Crouzeix_SpectralCauchy

set_option autoImplicit false
open Complex Polynomial spectrum
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
omit [CompleteSpace E]
theorem _root_.solution (A : E →L[ℂ] E) {c : ℂ} {r : ℝ}
    (hσ : spectrum ℂ A ⊆ Metric.ball c r) {z : ℂ} (hz : z ∉ Metric.ball c r) :
    z ∈ resolventSet ℂ A := by
  rw [mem_resolventSet_iff, ← spectrum.notMem_iff]
  exact fun h => hz (hσ h)
