-- Prove2me | Theorems.Thm_EinsteinFieldEquations_schwarzschild_ricci_flat
-- name    : EinsteinFieldEquations.schwarzschild_ricci_flat
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T00:49:34.248593+00:00
-- url     : https://prove2.me/theorems/3b3eb0f5-8669-4230-a0b4-c42ddd21ece2
-- title:
--   The Schwarzschild metric is Ricci-flat
-- statement:
--   **Ricci-flatness of the Schwarzschild metric.** For $M > 0$ and every point of the exterior region ($r > 2M$, $0 < \theta < \pi$), all components of the Ricci tensor of the Schwarzschild metric vanish:
--
--   $$R_{ab}\big(g^{\mathrm{Schw}}_{M}\big)(x) \;=\; 0 \qquad \text{for all } a, b \in \{0,1,2,3\}.$$
--
--   Equivalently, the Schwarzschild metric is a Ricci-flat (vacuum) metric on its exterior region. This is the computational heart of the mission: combined with the equivalence between the vacuum field equations and Ricci-flatness, it yields the goal theorem.
-- source:
--   Wikipedia, "Einstein field equations", https://en.wikipedia.org/wiki/Einstein_field_equations, section "Vacuum field equations" ("Nontrivial examples include the Schwarzschild solution"); Wikipedia, "General relativity", https://en.wikipedia.org/wiki/General_relativity, section "Solutions"

import Definitions.Def_efe_metrics

namespace EinsteinFieldEquations

theorem schwarzschild_ricci_flat (M : ℝ) (x : Coord) (hM : 0 < M)
    (hx : SchwarzschildExterior M x) :
    ∀ a b : Fin 4, ricci (schwarzschild M) a b x = 0 := by sorry

end EinsteinFieldEquations
