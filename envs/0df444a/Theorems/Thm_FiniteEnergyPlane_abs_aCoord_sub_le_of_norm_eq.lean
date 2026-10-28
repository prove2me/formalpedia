-- Prove2me | Theorems.Thm_FiniteEnergyPlane_abs_aCoord_sub_le_of_norm_eq
-- name    : FiniteEnergyPlane.abs_aCoord_sub_le_of_norm_eq
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-26T20:45:22.015372+00:00
-- url     : https://prove2.me/theorems/4b72cec9-4879-4c3c-bdc6-eb934f9f9e11
-- title:
--   Bounded oscillation of the symplectization coordinate on circles about a puncture
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb R^{2n+2}$ be a strictly star-shaped level with a $d\lambda$-compatible complex structure $J$ on $\xi$, and let $u=(a,w):\dot D=D\setminus\{0\}\to\mathbb R\times S\cong\mathbb R^{2n+2}\setminus\{0\}$ be a finite-energy $\tilde J$-holomorphic curve on the punctured unit disc. Assume the gradient bound $|z|\,|\nabla u(z)|\le C$ for $0<|z|<r$, where $|\nabla u|=\|Da\|+\|Dw\|$. Then the coordinate $a$ has oscillation at most $6\pi C$ on every circle about the puncture of radius less than $\min(r,1)$: if $z\neq0$, $|z|<r$, $|z|<1$ and $|z'|=|z|$, then $|a(u(z))-a(u(z'))|\le 6\pi C$.
--
--   This is used in the zero-charge case of the asymptotic description of finite-energy punctured discs (Hofer; Wendl, Theorem 9.8): it lets one choose circles about the puncture on which $a$ lies entirely on one side of a given level.
--
--   **Formalization Note** $\mathbb R\times S$ is identified with $\mathbb R^{2n+2}\setminus\{0\}$ by $(a,x)\mapsto e^{2a}x$; $a$ is `aCoord H` and $|\nabla u|$ is `gradNorm H u`. The bound $6\pi C$ is a convenient explicit constant.
-- source:
--   H. Hofer, Pseudoholomorphic curves in symplectizations with applications to the Weinstein conjecture in dimension three, Invent. Math. 114 (1993), 515-563, Section 3; C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, Lemmas 9.14 and 9.17

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Bounded oscillation of the symplectization coordinate on circles about the puncture: under
the gradient bound `‖z‖ · |∇u(z)| ≤ C` on `0 < ‖z‖ < r`, any two points `z, z'` on the same circle
`‖z'‖ = ‖z‖ < min r 1` satisfy `|a(u(z)) - a(u(z'))| ≤ 6πC`. -/
theorem abs_aCoord_sub_le_of_norm_eq {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u) (r C : ℝ)
    (hG : ∀ z : ℂ, z ≠ 0 → ‖z‖ < r → ‖z‖ * gradNorm H u z ≤ C)
    (z z' : ℂ) (hz : z ≠ 0) (hzr : ‖z‖ < r) (hz1 : ‖z‖ < 1) (hzz' : ‖z'‖ = ‖z‖) :
    |aCoord H (u z) - aCoord H (u z')| ≤ 6 * π * C := by
  sorry

end FiniteEnergyPlane
