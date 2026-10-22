-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_left_component_unique_ray_intersection
-- name    : BirkhoffGlobalSection.left_component_unique_ray_intersection
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T18:13:20.669612+00:00
-- url     : https://prove2.me/theorems/ab51b6c1-d58c-44a1-b628-b604f5ebd1d3
-- title:
--   Unique radial intersection of the subcritical component
-- statement:
--   Let $0<\mu<1$ and let $-c$ lie below the first critical value. Write $\Sigma_{\mu,c}$ for the selected Levi-Civita component and $S^3$ for the round sphere in its four real phase coordinates. Every ray from the origin with direction $u\in S^3$ intersects $\Sigma_{\mu,c}$ exactly once. Equivalently, any sphere-valued map on the component with the formula
--
--   $$
--   R(s)=\frac{s}{\sqrt{|z|^2+|w|^2}}
--   $$
--
--   is bijective. This is the ray-intersection content of the star-shapedness asserted in Proposition 2.4. It isolates the geometric step from construction and continuity of the radial normalization map.
-- source:
--   Joung--van Koert, Proposition 2.4 and its proof, https://arxiv.org/abs/2407.19159v3, PDF p. 7. The proof derives the star-shaped Levi-Civita component from Moser regularization and Frauenfelder--van Koert, Lemma 4.2.1.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

/-- Every direction meets the selected star-shaped component in exactly one
positive radial point, so any map with the radial formula is bijective. -/
theorem left_component_unique_ray_intersection (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (f : LeftEnergyState μ c → {x : Phase // x ∈ unitThreeSphere})
    (hrad : ∀ s, (f s : Phase) =
      fun i => (s : Phase) i /
        Real.sqrt (zNormSq (s : Phase) + wNormSq (s : Phase))) :
    Function.Bijective f := by sorry

end BirkhoffGlobalSection
