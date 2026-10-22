-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_model_rational_page_pulls_back
-- name    : BirkhoffGlobalSection.model_rational_page_pulls_back
-- status  : Proved
-- author  : @caleb
-- created : 2026-09-27T01:50:30.11299+00:00
-- url     : https://prove2.me/theorems/4eb53d0b-ca7a-4f8b-ba90-9aa59f959e7f
-- title:
--   Smooth pullback of a rational page through complete regularization clocks
-- statement:
--   Let $M$ be a convex regularization model of an antipodally invariant LC energy component. Let $\varphi$ be a flow on that component, let $D$ be complete model dynamics related to it by increasing onto clocks, and let $\gamma$ be a periodic orbit of $\varphi$.
--
--   Every rational page in the convex model pulls back to a lifted rational page for $\varphi$:
--
--   $$
--   \operatorname{ConvexModelRationalPage}(M,D,\gamma)
--   \quad\Longrightarrow\quad
--   \operatorname{Nonempty}\bigl(\operatorname{LiftedRationalPage}(\varphi,\gamma)\bigr).
--   $$
--
--   All clauses are transported: membership in the component, smoothness through the closed boundary, injectivity and immersion, interior transversality, the boundary orbit, exact antipodal fibers, and returns unbounded in both time directions.
--
--   This is a coordinate and time-change invariance theorem. It does not require the retrograde condition or assume page existence for either system; it applies to any supplied model rational page.
--
--   **Formalization Note.** Smooth maps are represented by ambient maps near the closed disk, and complete clocks are order isomorphisms of the real line.
-- source:
--   Elementary smooth coordinate and positive time-change invariance of the explicit model-page and lifted-page definitions. Motivated by the regularization transport needed for Liu--Salomao, https://arxiv.org/html/2506.17867v2, Theorem 1.16(ii). This is a new auxiliary transport theorem for the platform model, with a direct Lean proof based on the chain rule, local inverse identities, and order isomorphisms.

import Definitions.Def_BirkhoffGlobalSection_ConvexModelDynamics

namespace BirkhoffGlobalSection

/-- Pull back a model rational page by the smooth inverse regularization.
Order-isomorphism clocks preserve unbounded returns in both directions. -/
theorem model_rational_page_pulls_back {μ c : ℝ}
    (M : ConvexRegularizationModel μ c)
    (hinv : IsAntipodallyInvariantComponent μ c)
    (φ : Flow ℝ (LeftEnergyState μ c))
    (D : ConvexModelDynamics M φ) (γ : PeriodicOrbit φ)
    (P : ConvexModelRationalPage M D γ) :
    Nonempty (LiftedRationalPage φ γ) := by sorry

end BirkhoffGlobalSection
