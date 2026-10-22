-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_antipodal_trajectory_double_lift_is_double_cover
-- name    : BirkhoffGlobalSection.antipodal_trajectory_double_lift_is_double_cover
-- status  : Proved
-- author  : @Yivy Yu
-- created : 2026-09-12T15:09:28.002333+00:00
-- url     : https://prove2.me/theorems/6e46cb7d-b840-4149-b495-18594d15a8ac
-- title:
--   A prime quotient trajectory closes after two lifts
-- statement:
--   Let a prime trajectory in the antipodal quotient have period $P$, represented by a Levi-Civita lift $x$ with
--
--   $$
--   \varphi_P(x)=-x,
--   $$
--
--   and suppose no time $0<t<P$ reaches either $x$ or $-x$. If the antipodal action is free and the flow is equivariant, traversing the trajectory twice produces a closed Levi-Civita orbit of least period $2P$, with its antipodal point reached at half-period.
--
--   This isolates the elementary covering-space step from Birkhoff's geometric shooting theorem and from the open global-section assertion.
-- source:
--   Elementary covering-space consequence of the free antipodal double cover in Joung--van Koert, Proposition 2.4, https://arxiv.org/abs/2407.19159v3.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

/-- A prime antipodally closed trajectory becomes a least-period closed orbit
after traversing it twice on a free Levi-Civita cover. -/
theorem antipodal_trajectory_double_lift_is_double_cover {μ c : ℝ}
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hanti : IsAntipodallyEquivariantFlow μ c φ)
    (hfree : IsAntipodallyFreeComponent μ c)
    (δ : AntipodalPeriodicTrajectory φ) :
    IsAntipodalDoubleCover φ
      (antipodalTrajectoryDoubleLift φ hanti δ) := by sorry

end BirkhoffGlobalSection
