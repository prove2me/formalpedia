-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_periodic_orbit_transport
-- name    : BirkhoffGlobalSection.convex_model_periodic_orbit_transport
-- status  : Proved
-- author  : @caleb
-- created : 2026-09-27T02:10:27.549284+00:00
-- url     : https://prove2.me/theorems/38eede8b-13fe-4da8-a1a5-9cbf95f5f07b
-- title:
--   Complete clocks preserve prime periodic orbits and their geometric traces
-- statement:
--   Let $M$ be a convex regularization model and $D$ complete model dynamics for an LC flow $\varphi$. If $\gamma$ is a periodic orbit with least positive period $T$, its transported orbit has least positive period
--
--   $$
--   T_M=C_{\gamma(0)}(T),
--   $$
--
--   and its geometric trace is exactly
--
--   $$
--   \operatorname{orbit}(D_*\gamma)=F\bigl(\operatorname{orbit}(\gamma)\bigr).
--   $$
--
--   This is invariance of prime periodic orbits under an increasing complete trajectory clock and injective coordinate transport. It does not assert that the model Hamiltonian reaches its antipodal point at half of its period; a non-even Hamiltonian can use different clock speeds on the two halves.
--
--   **Formalization Note.** The transported orbit is the explicit `mapPeriodicOrbit` constructor. No Hamiltonian derivative, geometric retrograde condition, or page-existence assumption is needed beyond the supplied model-dynamics data.
-- source:
--   Elementary periodic-orbit transport under the complete order-isomorphism clocks in BirkhoffGlobalSection.ConvexModelDynamics. An auxiliary theorem proved directly from that interface; the regularization setting is Liu--Salomao, https://arxiv.org/html/2506.17867v2, Section 4. No external periodic-orbit theorem is assumed.

import Definitions.Def_BirkhoffGlobalSection_TransverseHopf

namespace BirkhoffGlobalSection

/-- Complete increasing clocks preserve least positive periods and transport
exactly the geometric trace of a closed orbit. -/
theorem convex_model_periodic_orbit_transport {μ c : ℝ}
    (M : ConvexRegularizationModel μ c)
    (φ : Flow ℝ (LeftEnergyState μ c)) (D : ConvexModelDynamics M φ)
    (γ : PeriodicOrbit φ) (hsimple : IsSimplePeriodicOrbit φ γ) :
    IsSimplePeriodicOrbit D.flow (D.mapPeriodicOrbit γ) ∧
      convexModelOrbitSet (D.mapPeriodicOrbit γ) = M.toModel '' orbitSet γ := by sorry

end BirkhoffGlobalSection
