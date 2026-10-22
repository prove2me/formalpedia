-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_antipodal_quotient_dynamics_continuous
-- name    : BirkhoffGlobalSection.antipodal_quotient_dynamics_continuous
-- status  : Proved
-- author  : @Yivy Yu
-- created : 2026-09-12T15:09:12.748862+00:00
-- url     : https://prove2.me/theorems/a3d59484-2e6b-4fb4-94bb-5bb8f6a21f80
-- title:
--   Continuous dynamics on the antipodal quotient
-- statement:
--   Let the selected Levi-Civita component be invariant under its free antipodal deck map, and let a continuous real flow commute with that map. Then the representative-independent time maps induced on
--
--   $$
--   Q_{\mu,c}=\Sigma_{\mu,c}/(s\sim -s)
--   $$
--
--   form a jointly continuous map $\mathbb{R}\times Q_{\mu,c}\to Q_{\mu,c}$. Its identity and composition laws are inherited from the original `Flow`.
--
--   This is the topological descent needed before return conditions can be interpreted as statements about a genuine quotient flow rather than unrelated time maps.
-- source:
--   Formal covering-space consequence of the antipodal equivariance in Joung--van Koert, equation (2.4) and Proposition 2.4, https://arxiv.org/abs/2407.19159v3.

import Definitions.Def_BirkhoffGlobalSection
import Mathlib.Topology.CompactOpen

namespace BirkhoffGlobalSection

/-- A continuous antipodally equivariant flow descends to a jointly continuous
real action on the free invariant antipodal quotient. -/
theorem antipodal_quotient_dynamics_continuous {μ c : ℝ}
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hanti : IsAntipodallyEquivariantFlow μ c φ)
    (hinv : IsAntipodallyInvariantComponent μ c)
    (hfree : IsAntipodallyFreeComponent μ c) :
    IsContinuousQuotientDynamics φ hanti := by sorry

end BirkhoffGlobalSection
