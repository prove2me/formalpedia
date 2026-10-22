-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_regularization_model_dynamics
-- name    : BirkhoffGlobalSection.convex_regularization_model_dynamics
-- status  : Proved
-- author  : @caleb
-- created : 2026-09-27T01:50:45.936525+00:00
-- url     : https://prove2.me/theorems/59f5c30e-50e6-4242-9fa9-a801fd79cf8a
-- title:
--   Complete Hamiltonian time change to a convex regularization model
-- statement:
--   Assume $0<\mu<1$ and $-c<h_1(\mu)$. Let $M$ be a convex regularization model and suppose its regularized time factor satisfies
--
--   $$
--   0<a\le\tau(s)\le b\qquad(s\in\Sigma_{\mu,c}).
--   $$
--
--   Every complete LC Hamiltonian flow $\varphi$ then admits complete model dynamics: a Hamiltonian flow $\psi$ on $\partial B$ and increasing onto clocks $C_s:\mathbb R\to\mathbb R$ with
--
--   $$
--   C_s(0)=0,\qquad C_s'(t)=\tau(\varphi_t(s)),\qquad
--   \psi_{C_s(t)}(F(s))=F(\varphi_t(s)).
--   $$
--
--   This is the analytic time-change obligation. It is independent of any chosen periodic orbit or spanning page. It asserts joint continuity and the flow law for the model dynamics, not merely the existence of a separate scalar clock along each orbit.
--
--   **Formalization Note.** The model dynamics are the structure `ConvexModelDynamics`; the formal hypotheses state finite real upper and lower clock bounds.
-- source:
--   Standard positive time-change construction specialized to the explicit convex regularization interface: C_s(t)=integral from 0 to t of tau(phi_u(s)) du, with inverse clocks defining the model flow. The regularized coordinate/time-change setting is Liu--Salomao, https://arxiv.org/html/2506.17867v2, Section 4. This is an auxiliary analytic theorem formulated for this decomposition, not a verbatim theorem in that paper.

import Definitions.Def_BirkhoffGlobalSection_ConvexModelDynamics

namespace BirkhoffGlobalSection

/-- A uniformly positive bounded regularized clock transports a complete
LC Hamiltonian flow to a complete Hamiltonian flow on the convex model. -/
theorem convex_regularization_model_dynamics
    (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (M : ConvexRegularizationModel μ c)
    (a b : ℝ) (ha : 0 < a)
    (hclock : ∀ s ∈ leftEnergyComponent μ c,
      a ≤ M.timeScale s ∧ M.timeScale s ≤ b)
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ) :
    Nonempty (ConvexModelDynamics M φ) := by sorry

end BirkhoffGlobalSection
