-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_positive_time_change_variational_matrix_reverse
-- name    : BirkhoffGlobalSection.positive_time_change_variational_matrix_reverse
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:14:38.56709+00:00
-- url     : https://prove2.me/theorems/86ba268b-2d6a-4b5c-86ad-0786f31a35c7
-- title:
--   Positive time change variational matrix reverse
-- statement:
--   For supplied scaled-field variational data and a complete positive clock, the stated inverse shear construction recovers the original-field variational matrix under the displayed regularity hypotheses.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 6 of the Proved theorem BirkhoffGlobalSection.positive_time_change_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_positive_time_change_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_positive_time_change_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

universe u_positive_time_change_variational_matrix_reverse

theorem BirkhoffGlobalSection.positive_time_change_variational_matrix_reverse :
∀ {E : Type u_positive_time_change_variational_matrix_reverse}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (X : E → E) (b : E → ℝ) (x : ℝ → E) (C : ℝ ≃o ℝ)
    (Z : ℝ → (E →L[ℝ] E))
    (hx : ∀ t, HasDerivAt x (X (x t)) t)
    (hC : ∀ t, HasDerivAt C (b (x t))⁻¹ t)
    (hZ : ∀ t, HasDerivAt Z
      ((fderiv ℝ (fun y => b y • X y) (x (C.symm t))).comp (Z t)) t)
    (hX : ∀ t, DifferentiableAt ℝ X (x t))
    (hb : ∀ t, DifferentiableAt ℝ b (x t))
    (hne : ∀ t, b (x t) ≠ 0)
    (hk : Continuous (fun t => (b (x t))⁻¹ •
      ((fderiv ℝ b (x t)).comp (Z (C t))))),
    let η : ℝ → (E →L[ℝ] ℝ) := fun t =>
      -(∫ s in (0 : ℝ)..t, (b (x s))⁻¹ • ((fderiv ℝ b (x s)).comp (Z (C s))))
    let Y : ℝ → (E →L[ℝ] E) := fun t => Z (C t) + (η t).smulRight (X (x t))
    Y 0 = Z (C 0) ∧
      ∀ t, HasDerivAt Y ((fderiv ℝ X (x t)).comp (Y t)) t := by sorry
