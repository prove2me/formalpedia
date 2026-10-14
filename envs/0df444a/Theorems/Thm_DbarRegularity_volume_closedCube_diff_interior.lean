-- Prove2me | Theorems.Thm_DbarRegularity_volume_closedCube_diff_interior
-- name    : DbarRegularity.volume_closedCube_diff_interior
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T15:31:51.136081+00:00
-- url     : https://prove2.me/theorems/75afd2b3-b498-4bde-9654-13319d1b0464
-- title:
--   The boundary of a closed cube in $\mathbb R^d$ is Lebesgue-null
-- statement:
--   Let $d\ge0$, $a\in\mathbb R^d$ and $s\in\mathbb R$, and let $Q=\prod_{i}[a_i,a_i+s]$ be the closed cube with corner $a$ and side $s$. Then the set $Q\setminus\operatorname{int}Q$ has Lebesgue measure zero.
--
--   So a closed cube and its interior agree up to a null set. Integrals and measures over closed cubes, for example those from a Calderón–Zygmund decomposition, can therefore be computed on the open cubes, which are pairwise disjoint whenever the closed cubes have disjoint interiors.
--
--   **Formalization Note.** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)` with Lebesgue measure `volume`. The cube is `closedCube a s = {x | ∀ i, a i ≤ x i ∧ x i ≤ a i + s}` from the mission's `Setting` definitions, and its interior is the topological `interior`.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton University Press (1970), Chapter I, § 3.1

import Definitions.Def_DbarRegularity_Setting
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

namespace DbarRegularity

open MeasureTheory Set

/-- The boundary `Q \ interior Q` of a closed cube `Q = ∏ᵢ [aᵢ, aᵢ + s]` in `ℝ^d` is a Lebesgue
null set. -/
theorem volume_closedCube_diff_interior {d : ℕ} (a : EuclideanSpace ℝ (Fin d)) (s : ℝ) :
    volume (closedCube a s \ interior (closedCube a s)) = 0 := by sorry

end DbarRegularity
