-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_geometric_retrograde_page_of_convex_regularization
-- name    : BirkhoffGlobalSection.geometric_retrograde_page_of_convex_regularization
-- status  : Open
-- author  : @caleb
-- created : 2026-09-27T01:35:43.510801+00:00
-- url     : https://prove2.me/theorems/e9163b74-94ef-45b6-a10d-2f864971217e
-- title:
--   Geometric retrograde pages from a convex regularization model
-- statement:
--   Let $0<\mu<1$ and $-c<h_1(\mu)$. Suppose the selected Levi-Civita component admits a convex regularization model $M$, and its regularized clock has uniform bounds
--
--   $$
--   0<a\le\tau(s)\le b<\infty\qquad (s\in\Sigma_{\mu,c}).
--   $$
--
--   For any complete Levi-Civita Hamiltonian flow commuting with the antipodal action, every geometric Birkhoff retrograde trajectory admits a lifted rational disk page over its closed double lift:
--
--   $$
--   \operatorname{Nonempty}\bigl(\operatorname{LiftedRationalPage}(\varphi,\widetilde\delta)\bigr).
--   $$
--
--   Here geometric retrograde means a collision-free simple projected loop of winding $+1$ with the specified reflection symmetry. The conclusion includes a smooth embedded immersed disk, interior transversality, precisely opposite boundary antipodal identifications, and unbounded returns in both time directions to the disk or its antipode.
--
--   This is the contact-topological and transport obligation complementary to local convex-model existence. It includes identifying the geometric orbit with the required transverse rational unknot of self-linking $-1/2$, obtaining an appropriate rational page on the convex regularization, and transporting the full smooth page data back to the Levi-Civita model. None of those identifications is a hypothesis disguised as a geometric winding condition, and none is claimed proved here.
--
--   **Formalization Note.** The clock bounds are explicit hypotheses. The geometric orbit condition permits temporary angular reversals and is not replaced by a pointwise angular-momentum inequality. The statement is a specialized transport formulation motivated by Theorem 1.16(ii), not a general assertion that every periodic orbit on a convex hypersurface binds a disk page.
-- source:
--   Liu--Salomao, https://arxiv.org/html/2506.17867v2, Theorem 1.16(ii) and Section 10, together with the retrograde-orbit disk discussion in Section 5. This specialized convex-model binding and transport lemma is formulated for the Prove2Me decomposition; proving the rational-unknot/self-linking identification and all transport clauses is an explicit obligation, not an already formalized application of the paper.

import Definitions.Def_BirkhoffGlobalSection_ConvexRegularizationModel
import Definitions.Def_BirkhoffGlobalSection_LiftedRationalPage

namespace BirkhoffGlobalSection

/-- The geometric retrograde binding criterion in a convex regularization.
Its proof includes the transverse rational-unknot/self-linking identification,
construction of a rational page, and smooth equivariant transport to LC
coordinates. Explicit clock bounds preserve unbounded returns both ways. -/
theorem geometric_retrograde_page_of_convex_regularization
    (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (M : ConvexRegularizationModel μ c)
    (a b : ℝ) (ha : 0 < a)
    (hclock : ∀ s ∈ leftEnergyComponent μ c,
      a ≤ M.timeScale s ∧ M.timeScale s ≤ b)
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ)
    (hanti : IsAntipodallyEquivariantFlow μ c φ)
    (δ : AntipodalPeriodicTrajectory φ)
    (hδ : IsGeometricBirkhoffRetrogradeTrajectory φ δ) :
    Nonempty (LiftedRationalPage φ
      (antipodalTrajectoryDoubleLift φ hanti δ)) := by sorry

end BirkhoffGlobalSection
