-- Prove2me | Theorems.Thm_DbarRegularity_volume_closedCube
-- name    : DbarRegularity.volume_closedCube
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-11T23:28:54.645047+00:00
-- url     : https://prove2.me/theorems/b90dbe5b-aab2-47a6-a263-61f8bd89647a
-- title:
--   Volume of a closed cube in ℝ^d
-- statement:
--   For $a\in\mathbb{R}^d$ and $s\in\mathbb{R}$ let $Q(a,s)=\{x\in\mathbb{R}^d:\ a_i\le x_i\le a_i+s\ \text{for all } i\}$ be the closed cube with corner $a$ and side length $s$. Then its Lebesgue measure is
--   $$|Q(a,s)| = (s^+)^d,$$
--   where $s^+=\max(s,0)$. In particular $|Q(a,s)|=s^d$ for $s\ge 0$.
--
--   This is the basic volume formula for coordinate cubes in $\mathbb{R}^d$.
--
--   **Formalization Note.** `closedCube a s` comes from `Definitions.Def_DbarRegularity_Setting`; $\mathbb{R}^d$ is `EuclideanSpace ℝ (Fin d)` with `volume` its Lebesgue measure, valued in `ℝ≥0∞`. The value $(s^+)^d$ is written `ENNReal.ofReal s ^ d`. No restriction on $d$ or $s$: for $d=0$ both sides equal $1$.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton Mathematical Series 30, Princeton University Press (1970), Chapter I, § 3.2, p. 16

import Definitions.Def_DbarRegularity_Setting

namespace DbarRegularity

open MeasureTheory
open scoped ENNReal

/-- The Lebesgue measure of the closed cube `∏ᵢ [aᵢ, aᵢ + s]` in `ℝ^d` is `s^d` (and `0` when
`s < 0` and `d ≥ 1`). -/
theorem volume_closedCube {d : ℕ} (a : EuclideanSpace ℝ (Fin d)) (s : ℝ) :
    volume (closedCube a s) = ENNReal.ofReal s ^ d := by sorry

end DbarRegularity
