-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_smooth_sphere_reeb_pushforward
-- name    : BirkhoffGlobalSection.convex_model_smooth_sphere_reeb_pushforward
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:16:33.083214+00:00
-- url     : https://prove2.me/theorems/616379fe-4337-40a8-96ee-a19d97ffc8fa
-- title:
--   Convex model smooth sphere reeb pushforward
-- statement:
--   The smooth sphere Reeb field for the convex model inverse-gauge weight pushes forward to its contact-normalized Hamiltonian vector field.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained. This is a conditional result for the defined convex regularization model, not a global-section or index-existence theorem.
-- source:
--   Independent extraction of component 6 of the Proved theorem BirkhoffGlobalSection.smooth_sphere_reeb_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_smooth_sphere_reeb_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_smooth_sphere_reeb_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.convex_model_smooth_sphere_reeb_pushforward :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u : Phase) (hu : u ∈ unitThreeSphere),
    let f : Phase → ℝ := fun x => ((gauge M.body x)⁻¹)^2
    let R : Phase → Phase := sphereReebExtension f
    let G : Phase → Phase := fun x => (gauge M.body x)⁻¹ • x
    let y := G u
    ContDiffAt ℝ ∞ R u ∧
      fderiv ℝ G u (R u) =
        (phaseRadialContact y (hamiltonianVectorField M.modelHamiltonian y))⁻¹ •
          hamiltonianVectorField M.modelHamiltonian y := by sorry
