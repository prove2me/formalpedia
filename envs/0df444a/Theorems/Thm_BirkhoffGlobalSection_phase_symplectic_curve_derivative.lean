-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_phase_symplectic_curve_derivative
-- name    : BirkhoffGlobalSection.phase_symplectic_curve_derivative
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:47:06.87698+00:00
-- url     : https://prove2.me/theorems/9a447f01-7eba-4e62-9384-be2d9161ad19
-- title:
--   Phase symplectic curve derivative
-- statement:
--   The symplectic pairing of two differentiable phase curves obeys the bilinear product-rule derivative formula.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 1 of the Proved theorem BirkhoffGlobalSection.variational_symplecticity_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_variational_symplecticity_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_variational_symplecticity_bundle
open BirkhoffGlobalSection Set Filter Topology
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.phase_symplectic_curve_derivative :
∀ (v w : ℝ → Phase) (t : ℝ) (a b : Phase)
    (hv : HasDerivAt v a t) (hw : HasDerivAt w b t),
    HasDerivAt (fun s => phaseSymplecticForm (v s) (w s))
      (phaseSymplecticForm a (w t) + phaseSymplecticForm (v t) b) t := by sorry
