-- Prove2me | Theorems.Thm_FiniteEnergyPlane_crApply_bijective_of_window
-- name    : FiniteEnergyPlane.crApply_bijective_of_window
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-12T18:10:22.263986+00:00
-- url     : https://prove2.me/theorems/e102d527-0b39-47e2-a173-b0ed2f795534
-- title:
--   Weighted normal Cauchy–Riemann operators with a winding window are bijective
-- statement:
--   Let $2 < p < \infty$. Let $S_\infty : \mathbb{R} \to \mathbb{R}^{2\times 2}$ be a smooth symmetric loop (`IsSymLoop`, entries $C^\infty$). Let $\delta \in \mathbb{R}$ be a weight such that $\delta$ is not an eigenvalue of the asymptotic operator $A_\infty = -J_0\partial_t - S_\infty$ on loops, every eigenvalue $\mu < \delta$ has eigenfunctions of winding $\le 0$, and every eigenvalue $\mu > \delta$ has eigenfunctions of winding $\ge 1$ (`IsLoopEigen`, `HasLoopEigenWind`). Let $S : \mathbb{R}^2 \to \mathbb{R}^{2\times 2}$ have $C^\infty$ entries, satisfy $S(s, t+1) = S(s,t)$, be exponentially asymptotic to $S_\infty$ at some rate $d > 0$ (`IsExpAsymptoticTo S Sinf d`), and be the pull-back of a smooth zero-order term on the plane (`IsPlaneCoeff S`). Let $\chi$ be a smooth weight with $\chi' = \pi$ on $(-\infty, -1]$ and $\chi' = \delta$ on $[1, \infty)$ (`IsSlopeWeight χ π δ`).
--
--   Then the operator
--   $$D w = \partial_s w + J_0 \partial_t w + \big(S(s,t) + \chi'(s)\big) w$$
--   (`crApply` with zero-order term $S + \chi'\,\mathbb{1}$) is a bijection from $W^{1,p}$ (`W1p p 1`) onto $L^p$ (`LpCyl 1 p`) on the cylinder: if $w \in W^{1,p}$ and $Dw = 0$ a.e., then $w = 0$; and every $f \in L^p$ equals $Dw$ a.e. for some $w \in W^{1,p}$.
--
--   **Role.** After conjugation by $e^{\chi}$ this is the normal Cauchy–Riemann operator along a holomorphic plane, on the space of sections that vanish to first order at $z = 0$ and decay like $e^{\delta s}$ at $\infty$. The winding window at $\delta$ is the condition under which it is an isomorphism.
-- source:
--   Toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076, Lemmas 6.10 and 6.20 (families of fast planes); operators in the setting of C. Wendl, Lectures on Holomorphic Curves in Symplectic and Contact Geometry, arXiv:1011.1690, Ch. 4

import Definitions.Def_FiniteEnergyPlane_TubeFamily

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology CauchyRiemannIndex
open scoped ContDiff ENNReal Real

/-- Let `p > 2`, `Sinf` a smooth symmetric loop with a winding window at `δ` (`δ` is not an
eigenvalue; eigenvalues below `δ` have winding `≤ 0`, those above have winding `≥ 1`), `S` a smooth
`1`-periodic coefficient exponentially asymptotic to `Sinf` that is the pull-back of a smooth
zero-order term on the plane, and `χ` a weight with slopes `π` and `δ`. Then
`∂ₛ + J₀ ∂ₜ + S + χ'(s)` is a bijection `W^{1,p} → L^p` on the cylinder. -/
theorem crApply_bijective_of_window (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 2 < p) (hp' : p ≠ ⊤)
    (Sinf : ℝ → Mat 1) (hSinf : IsSymLoop Sinf) (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (δ : ℝ) (hδe : ∀ e, ¬ IsLoopEigen Sinf δ e)
    (hwin : ∀ (μ : ℝ) (k : ℤ), HasLoopEigenWind Sinf μ k → (μ < δ ∧ k ≤ 0) ∨ (δ < μ ∧ 1 ≤ k))
    (S : ℝ × ℝ → Mat 1) (hS : ∀ i j, ContDiff ℝ ∞ (fun x : ℝ × ℝ => S x i j))
    (hSper : ∀ s t : ℝ, S (s, t + 1) = S (s, t))
    (d : ℝ) (hd : 0 < d) (hSas : IsExpAsymptoticTo S Sinf d) (hA : IsPlaneCoeff S)
    (χ : ℝ → ℝ) (hχ : IsSlopeWeight χ π δ) :
    (∀ w ∈ W1p p 1, crApply (fun x => S x + deriv χ x.1 • (1 : Mat 1)) w =ᵐ[cylMeasure] 0 →
        w = 0) ∧
      ∀ f : LpCyl 1 p, ∃ w ∈ W1p p 1,
        (f : ℝ × ℝ → Vec 1) =ᵐ[cylMeasure] crApply (fun x => S x + deriv χ x.1 • (1 : Mat 1)) w := by
  sorry

end FiniteEnergyPlane
