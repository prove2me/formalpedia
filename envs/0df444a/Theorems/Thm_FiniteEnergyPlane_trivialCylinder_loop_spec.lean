-- Prove2me | Theorems.Thm_FiniteEnergyPlane_trivialCylinder_loop_spec
-- name    : FiniteEnergyPlane.trivialCylinder_loop_spec
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-25T22:05:16.222986+00:00
-- url     : https://prove2.me/theorems/0e3a5a5a-2374-40e7-ad63-4f795caf8d4e
-- title:
--   Coordinates, loops and action of a reparametrized trivial cylinder
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb R^{2n+2}$ be a strictly star-shaped level. Let $P=(x,T)$ be a periodic Reeb orbit on $S$, $k\in\mathbb Z$, $c\in\mathbb C\setminus\{0\}$, and $F(z)=F_P(cz^k)$ for $z\ne0$, where $F_P(w)=|w|^{T/\pi}\,x\big(T\arg(w)/2\pi\big)$ is the trivial cylinder over $P$. Then:
--
--   1. for $z\ne0$, $F(z)\ne0$ and $a(F(z))=\dfrac{T}{2\pi}\log|cz^k|$;
--   2. there is $c'\in\mathbb R$ with $\mathrm{proj}\,F(e^{2\pi it})=x(kTt+c')$ for all $t\in\mathbb R$;
--   3. the action $\int_0^1\lambda_0(\gamma(t))(\gamma'(t))\,dt$ of $\gamma(t)=\mathrm{proj}\,F(e^{2\pi it})$ equals $kT$.
--
--   **Formalization Note** $F_P$ is `trivialCylinder P`, $a$ is `aCoord H`, the loop is `loopInS H F (ccwLoop 1)` and its action is `loopAction H F (ccwLoop 1)`.
-- source:
--   H. Hofer, Pseudoholomorphic curves in symplectizations with applications to the Weinstein conjecture in dimension three, Invent. Math. 114 (1993), 515–563, p. 537

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Coordinates and loops of a reparametrized trivial cylinder. Let `P = (x, T)` be a periodic
Reeb orbit, `k ∈ ℤ`, `c ∈ ℂ \ {0}`, and `F(z) = F_P(c z^k)` on `ℂ \ {0}`. Then `F(z) ≠ 0` and
`a(F(z)) = (T / 2π) log |c z^k|`; the loop `t ↦ proj F(e^{2π i t})` is `t ↦ x(k T t + c')` for some
`c' ∈ ℝ`; and its action is `k T`. -/
theorem trivialCylinder_loop_spec {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (P : ReebOrbit H) (k : ℤ) (c : ℂ) (hc : c ≠ 0) :
    (∀ z : ℂ, z ≠ 0 → trivialCylinder P (c * z ^ k) ≠ 0 ∧
      aCoord H (trivialCylinder P (c * z ^ k)) = P.T / (2 * π) * Real.log ‖c * z ^ k‖) ∧
    ∃ c' : ℝ, (∀ t : ℝ, loopInS H (fun z => trivialCylinder P (c * z ^ k)) (ccwLoop 1) t =
        P.x (k * P.T * t + c')) ∧
      loopAction H (fun z => trivialCylinder P (c * z ^ k)) (ccwLoop 1) = k * P.T := by
  sorry

end FiniteEnergyPlane
