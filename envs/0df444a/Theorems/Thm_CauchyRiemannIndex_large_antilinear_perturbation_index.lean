-- Prove2me | Theorems.Thm_CauchyRiemannIndex_large_antilinear_perturbation_index
-- name    : CauchyRiemannIndex.large_antilinear_perturbation_index
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-13T21:04:56.170649+00:00
-- url     : https://prove2.me/theorems/8a3b5383-52cc-4656-b24e-388cf7db5332
-- title:
--   Kernel and cokernel of Cauchy–Riemann operators with a large antilinear zeroth-order term
-- statement:
--   Let $n=1$, let $S^\pm$ be continuous loops of symmetric $2\times2$ matrices with nondegenerate asymptotic operators, and let $S:\mathbb{R}\times S^1\to\mathbb{R}^{2\times2}$ be continuous with $S(s,\cdot)\to S^\pm$ uniformly as $s\to\pm\infty$. Let $\beta:\mathbb{R}\times S^1\to\mathbb{C}$ be smooth with bounded first derivative, such that $|\beta|$ and $1/|\beta|$ are bounded for large $|s|$, and such that its zeros form finite sets $Z^+$ (positive zeros) and $Z^-$ (negative zeros) with the following normal form: for some $r>0$ and every $\zeta\in Z^\pm$, on the disc $|z|<r$ around $\zeta$ one has $S=0$ and
--   $$\beta(\zeta+z)=z\ \ (\zeta\in Z^+),\qquad\beta(\zeta+z)=\bar z\ \ (\zeta\in Z^-).$$
--   For $\sigma>0$ let $D_\sigma\eta=\partial_s\eta+J_0\partial_t\eta+S\eta+\sigma\beta\bar\eta$, acting from $W^{1,2}$ to $L^2$. Then:
--
--   1. if $Z^-=\emptyset$, then for all sufficiently large $\sigma$, $D_\sigma$ is surjective and $\dim\ker D_\sigma=\#Z^+$;
--   2. if $Z^+=\emptyset$, then for all sufficiently large $\sigma$, $D_\sigma$ is injective and $\dim\operatorname{coker}D_\sigma=\#Z^-$.
--
--   In either case $\operatorname{ind}D_\sigma=\#Z^+-\#Z^-$ for all sufficiently large $\sigma$.
--
--   **Formalization Note** $\mathbb{C}=\mathbb{R}^2$ via $(x,y)\mapsto x+iy$, and $\eta\mapsto\beta\bar\eta$ is the matrix `antilinearMat β`, so $D_\sigma$ is $D_{S_\sigma}$ with $S_\sigma=S+\sigma\cdot$`antilinearMat ∘ β`. Points of the cylinder are pairs $(s,t)$ and $\zeta+z$ means $(\zeta_s+\operatorname{Re}z,\zeta_t+\operatorname{Im}z)$; $\beta$ is $1$-periodic in $t$, the zeros are listed in $\mathbb{R}\times[0,1)$, and every zero of $\beta$ is a $t$-translate by an integer of a listed one. Wendl's § 5.5 asks, near each zero, for a holomorphic chart onto the unit disc in which $d\mathrm{vol}$ is standard, the operator is $\bar\partial$ and $\beta$ is $z$ or $\bar z$; here the chart is a translation of the coordinates $(s,t)$, the trivialization is the global one, and the area form is $ds\,dt$. Replacing the unit disc by a disc of radius $r$ rescales $\beta$ in the chart by $r^2$, which only reparametrizes $\sigma$, and kernels and cokernels do not depend on the area form. The exponent is $p=2$ (Wendl, Assumption 5.7). The conclusions are stated with `crRange 2 … = ⊤`, `crKernel 2 … = ⊥` and `finrank` of `crKernel 2 …` and of `LpCyl 1 2 ⧸ crRange 2 …`, together with their finite-dimensionality.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 5, Proposition 5.27, p. 102, with the assumptions of § 5.5, p. 94 (cylinder, trivial line bundle, p = 2)

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- Wendl, Proposition 5.27 (p. 102), with the assumptions of § 5.5 (p. 94), on the cylinder with the
trivial line bundle and `p = 2`: let `D_S` (`n = 1`) be asymptotic to nondegenerate loops `S±` of
symmetric matrices, and let `β : ℝ × S¹ → ℂ` be smooth with bounded derivative, with `|β|` and `1/|β|`
bounded for large `|s|`, whose zeros (mod `t ↦ t + 1`) are the finite sets `Z⁺` (positive zeros) and
`Z⁻` (negative zeros), such that on a disc of radius `r` around each zero `ζ` the operator is `∂̄`
(`S = 0`) and `β(ζ + z) = z` for `ζ ∈ Z⁺`, `β(ζ + z) = z̄` for `ζ ∈ Z⁻`. Put
`D_σ η = D_S η + σ β η̄`. If `Z⁻ = ∅`, then for all large `σ`, `D_σ : W^{1,2} → L²` is surjective with
`dim ker D_σ = #Z⁺`; if `Z⁺ = ∅`, then for all large `σ`, `D_σ` is injective with
`dim coker D_σ = #Z⁻`. -/
theorem large_antilinear_perturbation_index (Splus Sminus : ℝ → Mat 1) (hSplus : IsSymLoop Splus)
    (hSminus : IsSymLoop Sminus) (hplus : IsNondegenerate Splus) (hminus : IsNondegenerate Sminus)
    (S : ℝ × ℝ → Mat 1) (hS : IsAsymptoticTo S Splus Sminus)
    (β : ℝ × ℝ → ℂ) (hβ : ContDiff ℝ ∞ β) (hβper : ∀ s t, β (s, t + 1) = β (s, t))
    (hβC1 : ∃ C : ℝ, ∀ x, ‖fderiv ℝ β x‖ ≤ C)
    (hβends : ∃ (R c : ℝ), 0 < c ∧ ∀ s t, R ≤ |s| → c ≤ ‖β (s, t)‖ ∧ ‖β (s, t)‖ ≤ 1 / c)
    (Zplus Zminus : Finset (ℝ × ℝ)) (hZ : ∀ ζ ∈ Zplus ∪ Zminus, 0 ≤ ζ.2 ∧ ζ.2 < 1)
    (hdisj : Disjoint Zplus Zminus)
    (hzero : ∀ x : ℝ × ℝ, β x = 0 ↔ ∃ ζ ∈ Zplus ∪ Zminus, ∃ m : ℤ, x = (ζ.1, ζ.2 + m))
    (r : ℝ) (hr : 0 < r)
    (hplusZ : ∀ ζ ∈ Zplus, ∀ z : ℂ, ‖z‖ < r →
      β (ζ.1 + z.re, ζ.2 + z.im) = z ∧ S (ζ.1 + z.re, ζ.2 + z.im) = 0)
    (hminusZ : ∀ ζ ∈ Zminus, ∀ z : ℂ, ‖z‖ < r →
      β (ζ.1 + z.re, ζ.2 + z.im) = (starRingEnd ℂ) z ∧ S (ζ.1 + z.re, ζ.2 + z.im) = 0) :
    (Zminus = ∅ → ∃ σ₀ : ℝ, ∀ σ ≥ σ₀,
      crRange 2 (fun x => S x + σ • antilinearMat (β x)) = ⊤ ∧
      FiniteDimensional ℝ (crKernel 2 (fun x => S x + σ • antilinearMat (β x))) ∧
      Module.finrank ℝ (crKernel 2 (fun x => S x + σ • antilinearMat (β x))) = Zplus.card) ∧
    (Zplus = ∅ → ∃ σ₀ : ℝ, ∀ σ ≥ σ₀,
      crKernel 2 (fun x => S x + σ • antilinearMat (β x)) = ⊥ ∧
      FiniteDimensional ℝ (LpCyl 1 2 ⧸ crRange 2 (fun x => S x + σ • antilinearMat (β x))) ∧
      Module.finrank ℝ (LpCyl 1 2 ⧸ crRange 2 (fun x => S x + σ • antilinearMat (β x))) =
        Zminus.card) := by
  sorry

end CauchyRiemannIndex
