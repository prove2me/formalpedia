-- Prove2me | Theorems.Thm_FiniteEnergyPlane_eq_zero_of_crOp_window
-- name    : FiniteEnergyPlane.eq_zero_of_crOp_window
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-12T18:16:00.811738+00:00
-- url     : https://prove2.me/theorems/2edf317d-5275-4f80-9f5c-78bc63d93914
-- title:
--   No bounded solutions of the weighted normal operator under a winding window
-- statement:
--   Let $S_\infty : \mathbb{R} \to \mathbb{R}^{2\times 2}$ be a smooth symmetric loop and $\delta \in \mathbb{R}$ such that $\delta$ is not an eigenvalue of $A_\infty = -J_0\partial_t - S_\infty$, eigenvalues $\mu < \delta$ have eigenfunctions of winding $\le 0$ and eigenvalues $\mu > \delta$ have eigenfunctions of winding $\ge 1$. Let $S : \mathbb{R}^2 \to \mathbb{R}^{2\times 2}$ be smooth, $1$-periodic in $t$, exponentially asymptotic to $S_\infty$ at some rate $d > 0$ (`IsExpAsymptoticTo`), and of plane form (`IsPlaneCoeff S`: $S(s,t) = 4\pi\bar z A(z)$, $z = e^{2\pi(s+it)}$, $A$ smooth on $\mathbb{C}$). Let $\chi$ be smooth with $\chi' = \pi$ on $(-\infty,-1]$ and $\chi' = \delta$ on $[1,\infty)$ (`IsSlopeWeight χ π δ`), and write $D = \partial_s + J_0\partial_t + S + \chi'(s)$. Let $2 < p < \infty$, and let $g : \mathbb{R}^2 \to \mathbb{R}^2$ be $C^\infty$, $1$-periodic in $t$ and bounded, with $Dg = 0$ everywhere and $\partial_s g, \partial_t g \in L^p$ on the cylinder. Then $g \equiv 0$.
--
--   **Role.** Under $z = e^{2\pi(s+it)}$, $e^{\chi} g$ is a solution of a Cauchy–Riemann type equation on $\mathbb{C}^*$ that is small at $z = 0$ and decays like $e^{\delta s}$ at $\infty$. The statement says that the winding window at $\delta$ forbids nonzero solutions of this kind, which gives injectivity of the weighted normal operator.
-- source:
--   Toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076, Lemmas 6.10 and 6.20; operators in the setting of C. Wendl, Lectures on Holomorphic Curves in Symplectic and Contact Geometry, arXiv:1011.1690, Ch. 4

import Definitions.Def_FiniteEnergyPlane_TubeFamily

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set CauchyRiemannIndex
open scoped ContDiff ENNReal Real

/-- Let `Sinf` be a smooth symmetric loop with a winding window at `δ`, `S` a smooth `1`-periodic
coefficient exponentially asymptotic to `Sinf` and of plane form, and `χ` a weight with slopes `π`
and `δ`. Then every bounded smooth `1`-periodic solution `g` of `(∂ₛ + J₀ ∂ₜ + S + χ') g = 0` with
`∂ₛ g, ∂ₜ g ∈ L^p` (`2 < p < ∞`) vanishes identically. -/
theorem eq_zero_of_crOp_window (p : ℝ≥0∞) (hp : 2 < p) (hp' : p ≠ ⊤)
    (Sinf : ℝ → Mat 1) (hSinf : IsSymLoop Sinf) (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (δ : ℝ) (hδe : ∀ e, ¬ IsLoopEigen Sinf δ e)
    (hwin : ∀ (μ : ℝ) (k : ℤ), HasLoopEigenWind Sinf μ k → (μ < δ ∧ k ≤ 0) ∨ (δ < μ ∧ 1 ≤ k))
    (S : ℝ × ℝ → Mat 1) (hS : ∀ i j, ContDiff ℝ ∞ (fun x : ℝ × ℝ => S x i j))
    (hSper : ∀ s t : ℝ, S (s, t + 1) = S (s, t))
    (d : ℝ) (hd : 0 < d) (hSas : IsExpAsymptoticTo S Sinf d) (hA : IsPlaneCoeff S)
    (χ : ℝ → ℝ) (hχ : IsSlopeWeight χ π δ)
    (g : ℝ × ℝ → Vec 1) (hg : ContDiff ℝ ∞ g) (hgper : ∀ s t : ℝ, g (s, t + 1) = g (s, t))
    (B : ℝ) (hB : ∀ x, ‖g x‖ ≤ B)
    (heq : ∀ x, crOp (fun x => S x + deriv χ x.1 • (1 : Mat 1)) g x = 0)
    (hgs : MemLp (partialS g) p cylMeasure) (hgt : MemLp (partialT g) p cylMeasure) :
    ∀ x, g x = 0 := by
  sorry

end FiniteEnergyPlane
