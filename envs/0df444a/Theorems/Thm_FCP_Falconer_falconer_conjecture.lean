-- Prove2me | Theorems.Thm_FCP_Falconer_falconer_conjecture
-- name    : FCP.Falconer.falconer_conjecture
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-09-15T20:51:22.367171+00:00
-- url     : https://prove2.me/theorems/cb9bdc72-11a0-4cdb-a90f-c8f49d9cdcee
-- title:
--   Falconer's distance set conjecture
-- statement:
--   **Falconer's distance set conjecture.** If $E \subseteq \mathbb{R}^d$ is compact and $\dim_H E > d/2$, then the distance set $\Delta(E) = \{|x-y| : x, y \in E\}$ has positive Lebesgue measure. The threshold $d/2$ is sharp. The planar case is the most studied: Guth, Iosevich, Ou and Wang proved positive measure for $\dim_H E > 5/4$, and Falconer's original argument gives the exponent $d/2 + 1/2$ in general.
-- source:
--   Formal Conjectures library (Google DeepMind), Apache-2.0, https://github.com/google-deepmind/formal-conjectures (FormalConjectures/Wikipedia/Falconer.lean); K. Falconer, On the Hausdorff dimensions of distance sets, Mathematika 32 (1985), 206--212

import Mathlib

open MeasureTheory Set

open scoped ENNReal

namespace FCP.Falconer

theorem falconer_conjecture (d : ℕ) (E : Set (EuclideanSpace ℝ (Fin d))) (hc : IsCompact E)
    (hd : (d : ℝ≥0∞) < 2 * dimH E) : 0 < volume (image2 dist E E) := by sorry

end FCP.Falconer
