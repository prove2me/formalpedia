-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_left_energy_component_radial_bijection
-- name    : BirkhoffGlobalSection.left_energy_component_radial_bijection
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T17:44:52.104731+00:00
-- url     : https://prove2.me/theorems/541db2d1-6da2-4f8e-b773-fcae139a304c
-- title:
--   Radial projection of the subcritical Levi-Civita component
-- statement:
--   Let $0<\mu<1$, let $-c$ be below the first critical value, and let $\Sigma_{\mu,c}$ be the selected Levi-Civita energy component. Write $s=(z_1,z_2,w_1,w_2)$ and $r(s)=\sqrt{z_1^2+z_2^2+w_1^2+w_2^2}$. Radial normalization has a continuous bijective map to the unit three-sphere:
--
--   $$
--   R:\Sigma_{\mu,c}\longrightarrow S^3,\qquad R(s)=\frac{s}{r(s)}.
--   $$
--
--   The source establishes that this component is star-shaped below the first critical value. Every ray from the origin consequently meets its boundary once, giving the radial bijection. Positivity of the radius and continuity of normalization supply a continuous map. This isolates the geometric ray-intersection assertion from the topological step that a continuous bijection from a compact space to a Hausdorff space is a homeomorphism.
--
--   **Formalization Note.** The target records an explicit radial map into the round sphere rather than an unspecified equivalence.
-- source:
--   Joung--van Koert, Proposition 2.4 and proof, https://arxiv.org/abs/2407.19159v3, PDF p. 7; star-shapedness invokes Frauenfelder--van Koert, Lemma 4.2.1 as cited there. Radial projection is the explicit sphere parametrization of that star-shaped component.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

/-- The radial projection of the star-shaped subcritical component is a
continuous bijection onto the round unit three-sphere. -/
theorem left_energy_component_radial_bijection (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∃ f : LeftEnergyState μ c → {x : Phase // x ∈ unitThreeSphere},
      Continuous f ∧ Function.Bijective f ∧
        ∀ s, (f s : Phase) =
          fun i => (s : Phase) i /
            Real.sqrt (zNormSq (s : Phase) + wNormSq (s : Phase)) := by sorry

end BirkhoffGlobalSection
