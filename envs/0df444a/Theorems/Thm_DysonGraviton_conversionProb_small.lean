-- Prove2me | Theorems.Thm_DysonGraviton_conversionProb_small
-- name    : DysonGraviton.conversionProb_small
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T23:57:53.728231+00:00
-- url     : https://prove2.me/theorems/82653d3c-d2ea-4542-8bbf-074846fbcf9f
-- title:
--   Eqs. (28)–(30) — small-distance form of the Gertsenshtein conversion probability
-- statement:
--   Let $G, B, c > 0$ and $L = 2c^2/(G^{1/2}B)$. The conversion probability $P(D) = \sin^2(D/L)$ satisfies, for every $D$,
--   $$P(D) \le \frac{GB^2D^2}{4c^4},$$
--   and
--   $$\lim_{D\to 0^+} \frac{P(D)}{GB^2D^2/(4c^4)} = 1 .$$
-- source:
--   F. Dyson, Is a Graviton Detectable?, Int. J. Mod. Phys. A 28 (2013) 1330041, https://doi.org/10.1142/S0217751X1330041X, p. 10, Eqs. (28)–(30)

import Definitions.Def_DysonGraviton_Defs
import Mathlib

open MeasureTheory Filter Topology

namespace DysonGraviton

theorem conversionProb_small (G B c : ℝ) (hG : 0 < G) (hB : 0 < B) (hc : 0 < c) :
    (∀ D : ℝ, conversionProb G B c D ≤ G * B ^ 2 * D ^ 2 / (4 * c ^ 4)) ∧
    Tendsto (fun D : ℝ => conversionProb G B c D / (G * B ^ 2 * D ^ 2 / (4 * c ^ 4)))
      (𝓝[>] 0) (𝓝 1) := by
  sorry

end DysonGraviton
