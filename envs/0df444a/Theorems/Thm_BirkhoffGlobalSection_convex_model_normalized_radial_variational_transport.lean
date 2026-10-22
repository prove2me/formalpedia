-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_normalized_radial_variational_transport
-- name    : BirkhoffGlobalSection.convex_model_normalized_radial_variational_transport
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:16:07.796168+00:00
-- url     : https://prove2.me/theorems/874e4663-c0d7-4587-8ff7-310c5812b398
-- title:
--   Convex model normalized radial variational transport
-- statement:
--   Under the stated supplied sphere trajectory and variational hypotheses, the convex model radial chart transports the variation to the contact-normalized Hamiltonian field.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained. This is a conditional result for the defined convex regularization model, not a global-section or index-existence theorem.
-- source:
--   Independent extraction of component 8 of the Proved theorem BirkhoffGlobalSection.radial_variation_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_radial_variation_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_radial_variation_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.convex_model_normalized_radial_variational_transport :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (R : Phase → Phase) (q v : ℝ → Phase)
    (hqS : ∀ t, q t ∈ unitThreeSphere)
    (hvS : ∀ t, q t 0 * v t 0 + q t 1 * v t 1 +
      q t 2 * v t 2 + q t 3 * v t 3 = 0)
    (hR : ∀ t, DifferentiableAt ℝ R (q t))
    (hpush : ∀ z ∈ unitThreeSphere,
      let y := (gauge M.body z)⁻¹ • z
      fderiv ℝ (fun u : Phase => (gauge M.body u)⁻¹ • u) z (R z) =
        (phaseRadialContact y (hamiltonianVectorField M.modelHamiltonian y))⁻¹ •
          hamiltonianVectorField M.modelHamiltonian y)
    (hq : ∀ t, HasDerivAt q (R (q t)) t)
    (hv : ∀ t, HasDerivAt v (fderiv ℝ R (q t) (v t)) t),
    let G : Phase → Phase := fun u => (gauge M.body u)⁻¹ • u
    let X : Phase → Phase := fun y =>
      (phaseRadialContact y (hamiltonianVectorField M.modelHamiltonian y))⁻¹ •
        hamiltonianVectorField M.modelHamiltonian y
    (∀ t, HasDerivAt (fun s => G (q s)) (X (G (q t))) t) ∧
    (∀ t, HasDerivAt (fun s => fderiv ℝ G (q s) (v s))
      (fderiv ℝ X (G (q t)) (fderiv ℝ G (q t) (v t))) t) := by sorry
