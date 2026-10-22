-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_model_simple_periodic_orbit_exists
-- name    : BirkhoffGlobalSection.model_simple_periodic_orbit_exists
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-30T16:29:01.824638+00:00
-- url     : https://prove2.me/theorems/d983e864-a07f-4b2d-b47a-1750e75d1769
-- title:
--   Complete increasing clocks preserve prime periodic orbits
-- statement:
--   Let M be a smooth convex regularization model of a Levi–Civita energy component, phi a complete flow on the component, and D a complete model Hamiltonian flow related to phi by increasing onto trajectory clocks. If gamma is a periodic orbit of phi with least positive period T, then there is a prime model periodic orbit delta with the corresponding initial state and period
--
--   $$T_{\mathrm{model}}=C_{\gamma(0)}(T),$$
--
--   where C is the trajectory clock. Its geometric image is exactly the model-coordinate image of gamma.
--
--   This transports the primeness required by prescribed-binding criteria while preserving the orbit whose page must be constructed. It asserts neither orbit existence from parameters nor any knot, self-linking, or page property.
-- source:
--   Original auxiliary theorem for the existing ConvexModelDynamics interface, definition 264b7dde-5485-4fed-a4e6-553d4c3a5cfa, https://prove2.me/api/v1/theorems/264b7dde-5485-4fed-a4e6-553d4c3a5cfa. Motivated by the prime-orbit hypothesis of Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, https://arxiv.org/pdf/1105.2077v5, Section 1 and Theorem 1.7. This is an elementary time-change lemma, not a restatement of the analytic binding theorem.

import Definitions.Def_BirkhoffGlobalSection_ConvexModelDynamics

open BirkhoffGlobalSection

theorem BirkhoffGlobalSection.model_simple_periodic_orbit_exists {μ c : ℝ} (M : ConvexRegularizationModel μ c)
    (φ : Flow ℝ (LeftEnergyState μ c)) (D : ConvexModelDynamics M φ)
    (γ : PeriodicOrbit φ) (hγ : IsSimplePeriodicOrbit φ γ) :
    ∃ δ : PeriodicOrbit D.flow,
      δ.point = M.mapState γ.point ∧
      δ.period = D.clock γ.point γ.period ∧
      IsSimplePeriodicOrbit D.flow δ ∧
      Set.range (fun t : ℝ => ((D.flow t δ.point : ConvexModelState M) : Phase)) =
        M.toModel '' orbitSet γ := by sorry
