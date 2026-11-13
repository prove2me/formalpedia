-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_smooth_of_crApply_eq_zero
-- name    : FiniteEnergyPlane.exists_smooth_of_crApply_eq_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-12T18:14:23.320449+00:00
-- url     : https://prove2.me/theorems/ad823850-f9e7-456c-b5bd-faa37f526ad5
-- title:
--   Kernel elements of cylinder Cauchy–Riemann operators are smooth
-- statement:
--   Let $2 < p < \infty$ and let $M : \mathbb{R}^2 \to \mathbb{R}^{2\times 2}$ have $C^\infty$ entries with $M(s, t+1) = M(s,t)$. Let $w = (w_0, w_s, w_t) \in W^{1,p}$ (`W1p p 1`) on the cylinder satisfy
--   $$w_s + J_0 w_t + M w_0 = 0 \quad \text{a.e.}$$
--   (`crApply M w =ᵐ 0`). Then there is a $C^\infty$ map $g : \mathbb{R}^2 \to \mathbb{R}^2$ with $g(s, t+1) = g(s,t)$, $w_0 = g$ a.e., $\partial_s g + J_0\partial_t g + M g = 0$ everywhere (`crOp M g = 0`), and $\partial_s g, \partial_t g \in L^p$ on the cylinder.
--
--   **Role.** Elliptic regularity for kernel elements of Cauchy–Riemann type operators on the cylinder with smooth periodic coefficients, in the Sobolev setting of `CauchyRiemannIndex`. It turns a weak kernel element into a classical smooth solution with the same integrability.
-- source:
--   Toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076, Lemmas 6.10 and 6.20; operators in the setting of C. Wendl, Lectures on Holomorphic Curves in Symplectic and Contact Geometry, arXiv:1011.1690, Ch. 4

import Definitions.Def_FiniteEnergyPlane_TubeFamily

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set CauchyRiemannIndex
open scoped ContDiff ENNReal Real

/-- For `p > 2` and a smooth `1`-periodic coefficient `M`, every `w ∈ W^{1,p}` with
`(∂ₛ + J₀ ∂ₜ + M) w = 0` a.e. has a smooth `1`-periodic representative `g` of its first component
that solves `(∂ₛ + J₀ ∂ₜ + M) g = 0` everywhere, with `∂ₛ g, ∂ₜ g ∈ L^p` on the cylinder. -/
theorem exists_smooth_of_crApply_eq_zero (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 2 < p) (hp' : p ≠ ⊤)
    (M : ℝ × ℝ → Mat 1) (hM : ∀ i j, ContDiff ℝ ∞ (fun x : ℝ × ℝ => M x i j))
    (hMper : ∀ s t : ℝ, M (s, t + 1) = M (s, t))
    (w : Triple 1 p) (hw : w ∈ W1p p 1) (h0 : crApply M w =ᵐ[cylMeasure] 0) :
    ∃ g : ℝ × ℝ → Vec 1, ContDiff ℝ ∞ g ∧ (∀ s t : ℝ, g (s, t + 1) = g (s, t)) ∧
      (w.1 : ℝ × ℝ → Vec 1) =ᵐ[cylMeasure] g ∧ (∀ x, crOp M g x = 0) ∧
      MemLp (partialS g) p cylMeasure ∧ MemLp (partialT g) p cylMeasure := by
  sorry

end FiniteEnergyPlane
