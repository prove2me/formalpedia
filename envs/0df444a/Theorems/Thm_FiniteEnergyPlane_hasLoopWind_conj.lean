-- Prove2me | Theorems.Thm_FiniteEnergyPlane_hasLoopWind_conj
-- name    : FiniteEnergyPlane.hasLoopWind_conj
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-01T20:55:28.10042+00:00
-- url     : https://prove2.me/theorems/ae2b0078-22f1-401b-add6-ebcdd46525c4
-- title:
--   Complex conjugation negates the winding number of a loop
-- statement:
--   Let $f:\mathbb{R}\to\mathbb{C}$ be a continuous $1$-periodic nowhere-zero loop with winding number $k$. Then its complex conjugate $t\mapsto\overline{f(t)}$ has winding number $-k$.
--
--   Behaviour of the winding number under complex conjugation, for comparing windings of loops in $\mathbb{C}\setminus\{0\}$.
--
--   **Formalization Note** Hypothesis and conclusion are `HasLoopWind f k` and `HasLoopWind (fun t => starRingEnd ℂ (f t)) (-k)` from `FiniteEnergyPlane_Winding`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory (2026 notes), arXiv:1612.01009, Section 3.7 (winding numbers of loops in C minus 0); standard.

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

/-- Complex conjugation reverses the winding number of a loop in `ℂ \ {0}`. -/
theorem hasLoopWind_conj {f : ℝ → ℂ} {k : ℤ} (hf : HasLoopWind f k) :
    HasLoopWind (fun t => starRingEnd ℂ (f t)) (-k) := by
  sorry

end FiniteEnergyPlane
