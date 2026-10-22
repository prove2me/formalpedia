-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_left_component_radial_projection_continuous
-- name    : BirkhoffGlobalSection.left_component_radial_projection_continuous
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T18:13:17.977724+00:00
-- url     : https://prove2.me/theorems/4173a459-f676-40ee-8298-08469ed41fab
-- title:
--   Continuous radial normalization of the Levi-Civita component
-- statement:
--   Let $0<\mu<1$ and let $-c$ lie below the first critical value. Write $\Sigma_{\mu,c}$ for the selected Levi-Civita component and $S^3$ for the round sphere in its four real phase coordinates. Radial normalization defines a continuous map
--
--   $$
--   R:\Sigma_{\mu,c}\longrightarrow S^3,\qquad
--   R(s)=\frac{s}{\sqrt{|z|^2+|w|^2}}.
--   $$
--
--   In particular, no point of the selected component has zero radial denominator. This isolates the well-definedness and continuity of the explicit map; no ray-intersection or bijectivity claim is included. It is the analytic preparation for the star-shaped sphere model.
-- source:
--   Joung--van Koert, Proposition 2.4 and its proof, https://arxiv.org/abs/2407.19159v3, PDF p. 7. The proof derives the star-shaped Levi-Civita component from Moser regularization and Frauenfelder--van Koert, Lemma 4.2.1.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

/-- Radial normalization of the nonzero states on the selected component
lands on the unit sphere and varies continuously. -/
theorem left_component_radial_projection_continuous (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∃ f : LeftEnergyState μ c → {x : Phase // x ∈ unitThreeSphere},
      Continuous f ∧
        ∀ s, (f s : Phase) =
          fun i => (s : Phase) i /
            Real.sqrt (zNormSq (s : Phase) + wNormSq (s : Phase)) := by sorry

end BirkhoffGlobalSection
