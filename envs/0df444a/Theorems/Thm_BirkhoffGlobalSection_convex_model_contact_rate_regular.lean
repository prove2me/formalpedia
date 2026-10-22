-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_contact_rate_regular
-- name    : BirkhoffGlobalSection.convex_model_contact_rate_regular
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:15:24.476988+00:00
-- url     : https://prove2.me/theorems/7519f59f-bbb6-4c31-b996-75a509596d97
-- title:
--   Convex model contact rate regular
-- statement:
--   The convex model's Hamiltonian contact rate is smooth and positive at each boundary point.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained. This is a conditional result for the defined convex regularization model, not a global-section or index-existence theorem.
-- source:
--   Independent extraction of component 3 of the Proved theorem BirkhoffGlobalSection.model_contact_rate_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_model_contact_rate_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_model_contact_rate_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.convex_model_contact_rate_regular :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (y : Phase) (hy : y ∈ frontier M.body),
    let r : Phase → ℝ := fun x =>
      phaseRadialContact x (hamiltonianVectorField M.modelHamiltonian x)
    ContDiffAt ℝ ∞ (hamiltonianVectorField M.modelHamiltonian) y ∧
      ContDiffAt ℝ ∞ r y ∧ ContDiffAt ℝ ∞ (fun x => (r x)⁻¹) y ∧
      0 < (r y)⁻¹ := by sorry
