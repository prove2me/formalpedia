-- Prove2me | Theorems.Thm_FiniteEnergyPlane_fredholm_index_zero_of_window
-- name    : FiniteEnergyPlane.fredholm_index_zero_of_window
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-12T18:17:40.196878+00:00
-- url     : https://prove2.me/theorems/f0754cf2-33cf-4585-829c-03344cda03db
-- title:
--   The weighted normal operator under a winding window is Fredholm of index zero
-- statement:
--   Let $S_\infty : \mathbb{R} \to \mathbb{R}^{2\times 2}$ be a smooth symmetric loop and $\delta \in \mathbb{R}$ such that $\delta$ is not an eigenvalue of $A_\infty = -J_0\partial_t - S_\infty$, eigenvalues $\mu < \delta$ have eigenfunctions of winding $\le 0$ and eigenvalues $\mu > \delta$ have eigenfunctions of winding $\ge 1$. Let $S : \mathbb{R}^2 \to \mathbb{R}^{2\times 2}$ be smooth, $1$-periodic in $t$, exponentially asymptotic to $S_\infty$ at some rate $d > 0$ (`IsExpAsymptoticTo`), and of plane form (`IsPlaneCoeff S`: $S(s,t) = 4\pi\bar z A(z)$, $z = e^{2\pi(s+it)}$, $A$ smooth on $\mathbb{C}$). Let $\chi$ be smooth with $\chi' = \pi$ on $(-\infty,-1]$ and $\chi' = \delta$ on $[1,\infty)$ (`IsSlopeWeight χ π δ`), and write $D = \partial_s + J_0\partial_t + S + \chi'(s)$. Let $1 < p < \infty$. Then $D : W^{1,p} \to L^p$ is Fredholm (`IsFredholmCR`) and its index is $0$ (`crIndex`).
--
--   **Role.** The index count for the weighted normal operator along a holomorphic plane: the window at $\delta$ at the end $s = +\infty$ and the slope $\pi$ at the removable end $s = -\infty$ balance to index $0$. Combined with injectivity, this gives bijectivity.
-- source:
--   Toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076, Lemmas 6.10 and 6.20; operators in the setting of C. Wendl, Lectures on Holomorphic Curves in Symplectic and Contact Geometry, arXiv:1011.1690, Ch. 4

import Definitions.Def_FiniteEnergyPlane_TubeFamily

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set CauchyRiemannIndex
open scoped ContDiff ENNReal Real

/-- Under the same hypotheses on `Sinf`, `S` and `χ`, and for `1 < p < ∞`, the operator
`∂ₛ + J₀ ∂ₜ + S + χ' : W^{1,p} → L^p` is Fredholm of index `0`. -/
theorem fredholm_index_zero_of_window (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hp' : p ≠ ⊤)
    (Sinf : ℝ → Mat 1) (hSinf : IsSymLoop Sinf) (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (δ : ℝ) (hδe : ∀ e, ¬ IsLoopEigen Sinf δ e)
    (hwin : ∀ (μ : ℝ) (k : ℤ), HasLoopEigenWind Sinf μ k → (μ < δ ∧ k ≤ 0) ∨ (δ < μ ∧ 1 ≤ k))
    (S : ℝ × ℝ → Mat 1) (hS : ∀ i j, ContDiff ℝ ∞ (fun x : ℝ × ℝ => S x i j))
    (hSper : ∀ s t : ℝ, S (s, t + 1) = S (s, t))
    (d : ℝ) (hd : 0 < d) (hSas : IsExpAsymptoticTo S Sinf d) (hA : IsPlaneCoeff S)
    (χ : ℝ → ℝ) (hχ : IsSlopeWeight χ π δ) :
    IsFredholmCR p (fun x => S x + deriv χ x.1 • (1 : Mat 1)) ∧
      crIndex p (fun x => S x + deriv χ x.1 • (1 : Mat 1)) = 0 := by
  sorry

end FiniteEnergyPlane
