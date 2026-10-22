-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_quotient_page_lifts_to_cover
-- name    : BirkhoffGlobalSection.quotient_page_lifts_to_cover
-- status  : Proved
-- author  : @caleb
-- created : 2026-09-26T20:42:13.944948+00:00
-- url     : https://prove2.me/theorems/9093288c-158d-4ce7-b238-4aa88c8ffe1f
-- title:
--   Quotient page lifts to a cover-level rational page
-- statement:
--   This is the covering-theory lift behind the Levi-Civita transport: a quotient page ascends to the cover.
--
--   Let $\varphi$ be a flow on the selected Levi-Civita component with antipodal equivariance, and suppose the component is antipodally invariant and free, the descended quotient dynamics are jointly continuous, and $\gamma$ is a closed orbit whose half-period image is a prime quotient binding (i.e. $\gamma$ is an antipodal double cover). If $\gamma$ bounds a rational disk-like global surface of section $Q$ in the antipodal quotient, then there exists a lifted rational page upstairs: a smooth embedded immersed disk with boundary $\gamma$, transverse interior, exactly opposite-boundary antipodal identifications, and two-sided unbounded returns against either deck lift of its interior.
--
--   The content is the standard path-lifting argument through the free double cover identified in Joung--van Koert Proposition 2.4: the quotient disk lifts to a smooth immersed disk because the cover is a local homeomorphism, the boundary lifts to the closed double orbit by the prime-binding hypothesis, antipodal fibers upstairs are exactly the opposite-boundary pairs because the deck action is free, and transversality plus unbounded returns pull back under the covering projection.
--
--   **Formalization Note** Lean packages the upstairs data as the mission's `LiftedRationalPage` structure and the quotient data as `RationalDiskLikeGlobalSurfaceOfSection`.
-- source:
--   Joung--van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 2.4; standard covering-space path lifting for the free antipodal double cover.

import Definitions.Def_BirkhoffGlobalSection_LiftedRationalPage

import Definitions.Def_BirkhoffGlobalSection_LiftedRationalPage

namespace BirkhoffGlobalSection

/-- A rational quotient page lifts through the free invariant antipodal cover
to a smooth lifted rational two-disk page with two-sided returns. -/
theorem quotient_page_lifts_to_cover {μ c : ℝ} (φ : Flow ℝ (LeftEnergyState μ c))
    (hanti : IsAntipodallyEquivariantFlow μ c φ)
    (hinv : IsAntipodallyInvariantComponent μ c)
    (hfree : IsAntipodallyFreeComponent μ c)
    (hcont : IsContinuousQuotientDynamics φ hanti)
    (γ : PeriodicOrbit φ) (hdouble : IsAntipodalDoubleCover φ γ)
    (Q : RationalDiskLikeGlobalSurfaceOfSection φ hanti γ) :
    Nonempty (LiftedRationalPage φ γ) := by sorry

end BirkhoffGlobalSection
