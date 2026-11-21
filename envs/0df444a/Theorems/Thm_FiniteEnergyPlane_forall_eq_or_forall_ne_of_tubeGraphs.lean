-- Prove2me | Theorems.Thm_FiniteEnergyPlane_forall_eq_or_forall_ne_of_tubeGraphs
-- name    : FiniteEnergyPlane.forall_eq_or_forall_ne_of_tubeGraphs
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-16T20:14:12.561589+00:00
-- url     : https://prove2.me/theorems/95e9b5b2-0140-4c38-a7fb-7930bbbdce33
-- title:
--   Holomorphic graphs in a standard tube coincide or are disjoint
-- statement:
--   Let $(\bar J, J_\infty, S_\infty)$ be a standard tube structure of width $\rho$ and rate $b > 0$ on $\mathbb{C} \times \mathbb{C}$ (`IsStdTubeStructure ρ b Jbar Jinf Sinf`), and let $\delta < 0$ be such that every eigenfunction of the loop operator $-J_0 \frac{d}{dt} - S_\infty$ with eigenvalue $\mu \le \delta$ has winding at most $0$.
--
--   For $i = 1, 2$ let $\psi_i$ be a homeomorphism of $\mathbb{C}$, smooth with smooth inverse, and $v_i : \mathbb{C} \to B_\rho(0)$ smooth, such that $z \mapsto (\psi_i(z), v_i(z))$ is $\bar J$-holomorphic, and such that, in the coordinates $z = e^{2\pi(s+it)}$, $\psi_i(z)/z - \kappa_i$ decays exponentially in $C^\infty$ for some $\kappa_i \neq 0$ and $v_i(z)$ decays like $e^{\delta s}$ in $C^\infty$.
--
--   Then either $v_2(z) = v_1(\psi_1^{-1}(\psi_2(z)))$ for every $z \in \mathbb{C}$, or $v_2(z) \neq v_1(\psi_1^{-1}(\psi_2(z)))$ for every $z \in \mathbb{C}$. Equivalently, the image of the second graph either lies in the image of the first, or the two images are disjoint.
--
--   **Role.** A local "equal or disjoint" statement for holomorphic graphs in a standard tube, with the asymptotic condition at $\infty$ expressed through the windings of the limit operator $S_\infty$.
--
--   **Formalization Note.** The complex structure $i$ on the domain is `Complex.I • ContinuousLinearMap.id ℝ ℂ`; exponential $C^\infty$ decay in the cylindrical coordinate `cylInf s t` is `ExpDecayCInfty` (rate $b_i$ for $\psi_i$, rate $-\delta$ for $v_i$). The winding condition is stated with `HasLoopEigenWind Sinf μ k → k ≤ 0`.
-- source:
--   Toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076, Section 6 (Lemmas 6.23-6.25); asymptotic operators and windings as in H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations II, GAFA 5 (1995)

import Definitions.Def_FiniteEnergyPlane_Tube

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Two graphs `z ↦ (ψᵢ z, vᵢ z)` that are holomorphic for a standard tube structure `Jbar`,
with `ψᵢ` diffeomorphisms of `ℂ` asymptotic to `z ↦ κᵢ z` and `vᵢ` decaying like `e^{δ s}` in
cylindrical coordinates, where the loop eigenfunctions of `Sinf` with eigenvalue at most `δ` have
winding at most `0`: the second graph either lies on the first everywhere or nowhere. -/
theorem forall_eq_or_forall_ne_of_tubeGraphs (ρ b : ℝ) (hb : 0 < b)
    (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (hT : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    (δ : ℝ) (hδ : δ < 0) (hwind : ∀ μ ≤ δ, ∀ k : ℤ, HasLoopEigenWind Sinf μ k → k ≤ 0)
    (ψ₁ ψ₂ : ℂ ≃ₜ ℂ) (v₁ v₂ : ℂ → ℂ) (κ₁ κ₂ : ℂ) (b₁ b₂ : ℝ)
    (hψ₁ : ContDiff ℝ ∞ ψ₁) (hψ₁' : ContDiff ℝ ∞ ψ₁.symm) (hv₁ : ContDiff ℝ ∞ v₁)
    (hψ₂ : ContDiff ℝ ∞ ψ₂) (hψ₂' : ContDiff ℝ ∞ ψ₂.symm) (hv₂ : ContDiff ℝ ∞ v₂)
    (hv₁ρ : ∀ z, v₁ z ∈ ball (0 : ℂ) ρ) (hv₂ρ : ∀ z, v₂ z ∈ ball (0 : ℂ) ρ)
    (hhol₁ : ∀ z, (fderiv ℝ (fun x : ℂ => (ψ₁ x, v₁ x)) z).comp
        (Complex.I • ContinuousLinearMap.id ℝ ℂ) =
      (Jbar (ψ₁ z, v₁ z)).comp (fderiv ℝ (fun x : ℂ => (ψ₁ x, v₁ x)) z))
    (hhol₂ : ∀ z, (fderiv ℝ (fun x : ℂ => (ψ₂ x, v₂ x)) z).comp
        (Complex.I • ContinuousLinearMap.id ℝ ℂ) =
      (Jbar (ψ₂ z, v₂ z)).comp (fderiv ℝ (fun x : ℂ => (ψ₂ x, v₂ x)) z))
    (hκ₁ : κ₁ ≠ 0) (hb₁ : 0 < b₁)
    (hψ₁as : ExpDecayCInfty (fun p : ℝ × ℝ => ψ₁ (cylInf p.1 p.2) / cylInf p.1 p.2 - κ₁) b₁)
    (hv₁as : ExpDecayCInfty (fun p : ℝ × ℝ => v₁ (cylInf p.1 p.2)) (-δ))
    (hκ₂ : κ₂ ≠ 0) (hb₂ : 0 < b₂)
    (hψ₂as : ExpDecayCInfty (fun p : ℝ × ℝ => ψ₂ (cylInf p.1 p.2) / cylInf p.1 p.2 - κ₂) b₂)
    (hv₂as : ExpDecayCInfty (fun p : ℝ × ℝ => v₂ (cylInf p.1 p.2)) (-δ)) :
    (∀ z, v₂ z = v₁ (ψ₁.symm (ψ₂ z))) ∨ ∀ z, v₂ z ≠ v₁ (ψ₁.symm (ψ₂ z)) := by
  sorry

end FiniteEnergyPlane
