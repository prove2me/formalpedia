-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_model_ordinary_page_pulls_back
-- name    : BirkhoffGlobalSection.model_ordinary_page_pulls_back
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-30T16:31:05.625363+00:00
-- url     : https://prove2.me/theorems/9359f51d-b086-40de-9d23-7e29160c658e
-- title:
--   Ordinary global sections survive smooth regularization and complete clocks
-- statement:
--   Let M be a smooth convex regularization model of a Levi–Civita energy component, let phi be a complete flow on that component, and let D be complete model Hamiltonian dynamics conjugate to phi through increasing onto trajectory clocks. Let gamma be any periodic orbit of phi. If p is an ordinary model disk page with boundary the model image of gamma, then
--
--   $$q=M^{-1}\circ p$$
--
--   is an ordinary disk-like global surface of section for phi with binding gamma. The disk remains smooth, embedded and immersed through its boundary, its interior is transverse to the Levi–Civita Hamiltonian vector field, and every trajectory outside gamma meets its interior at arbitrarily large positive and negative times.
--
--   This is a transport theorem with page-existence data as an explicit input. It preserves returns to the same page, and imposes no additional antipodal-invariance assumption. It is useful when a prescribed-binding criterion first produces a section in regularized model coordinates.
--
--   **Formalization Note** The conclusion is the existing predicate DiskLikeGlobalSurfaceOfSection. The trajectory clocks are order isomorphisms of the real line.
-- source:
--   Ordinary-page adaptation of caleb’s accepted BirkhoffGlobalSection.model_rational_page_pulls_back proof, submission f60b661a-fad7-4713-aa8b-33ee4b295579, https://prove2.me/api/v1/submissions/f60b661a-fad7-4713-aa8b-33ee4b295579/solution. Uses the existing smooth regularization and complete-clock interfaces. This is an auxiliary transport result for Joung–van Koert, https://arxiv.org/abs/2407.19159v3, Theorems 1.2 and 1.5; not a verbatim source theorem or a page-existence claim.

import Definitions.Def_BirkhoffGlobalSection_ConvexModelOrdinaryPage

open scoped ContDiff Topology
open BirkhoffGlobalSection

theorem BirkhoffGlobalSection.model_ordinary_page_pulls_back {μ c : ℝ} (M : ConvexRegularizationModel μ c)
    (φ : Flow ℝ (LeftEnergyState μ c)) (D : ConvexModelDynamics M φ)
    (γ : PeriodicOrbit φ) (P : ConvexModelOrdinaryPage M D γ) :
    DiskLikeGlobalSurfaceOfSection φ γ := by sorry
