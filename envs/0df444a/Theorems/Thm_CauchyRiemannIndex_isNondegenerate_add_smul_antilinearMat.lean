-- Prove2me | Theorems.Thm_CauchyRiemannIndex_isNondegenerate_add_smul_antilinearMat
-- name    : CauchyRiemannIndex.isNondegenerate_add_smul_antilinearMat
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-17T16:37:00.875852+00:00
-- url     : https://prove2.me/theorems/77a86d41-f530-4e3e-a10f-c6cc80d7e7ff
-- title:
--   Asymptotic operators with a large antilinear term are nondegenerate
-- statement:
--   Let $T:\mathbb{R}\to\mathbb{R}^{2\times 2}$ be pointwise symmetric with all entries bounded by $K$, and let $\gamma:\mathbb{R}\to\mathbb{C}$ be differentiable and $1$-periodic with $m\le|\gamma(t)|$ and $|\gamma'(t)|\le D$ for all $t$, where $m\ge 0$. If $\sigma>0$ and
--   $$4K^2+2\sigma D<\sigma^2 m^2,$$
--   then the asymptotic operator $\eta\mapsto -J_0\dot\eta - T\eta - \sigma\gamma\bar\eta$ on loops $\eta:S^1\to\mathbb{C}=\mathbb{R}^2$ is nondegenerate.
--
--   This gives an explicit size of the antilinear term beyond which nondegeneracy holds, uniformly over all coefficients $T$ and loops $\gamma$ with the same bounds $K$, $m$, $D$.
--
--   **Formalization Note** The operator is `fun t => T t + σ • antilinearMat (γ t)`, where `antilinearMat β` is the real matrix of $z\mapsto\beta\bar z$. `IsNondegenerate` is stated through the fundamental solution $\Psi'=J_0(T+\sigma B_\gamma)\Psi$, $\Psi(0)=\mathrm{Id}$: $\det(\mathrm{Id}-\Psi(1))\ne 0$. Continuity and periodicity of $T$ are not assumed. The derivative is given as `HasDerivAt γ (γ' t) t`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 5, §5.8, pp. 102-103

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace CauchyRiemannIndex

open Matrix

/-- Let `T : ℝ → ℝ^{2×2}` be pointwise symmetric with entries bounded by `K`, and let
`γ : ℝ → ℂ` be a differentiable `1`-periodic loop with `m ≤ |γ(t)|` (`m ≥ 0`) and
`|γ'(t)| ≤ D`. If `σ > 0` and `4K² + 2σD < σ²m²`, then the asymptotic operator
`η ↦ -J₀ η' - T η - σ γ η̄` is nondegenerate. -/
theorem isNondegenerate_add_smul_antilinearMat (T : ℝ → Mat 1) (hT : ∀ t, (T t).IsSymm)
    (K : ℝ) (hK : ∀ t i j, |T t i j| ≤ K) (γ γ' : ℝ → ℂ) (hγ : ∀ t, HasDerivAt γ (γ' t) t)
    (hper : Function.Periodic γ 1) (m D : ℝ) (hm0 : 0 ≤ m) (hm : ∀ t, m ≤ ‖γ t‖)
    (hD : ∀ t, ‖γ' t‖ ≤ D) (σ : ℝ) (hσ : 0 < σ)
    (hbig : 4 * K ^ 2 + 2 * σ * D < σ ^ 2 * m ^ 2) :
    IsNondegenerate (fun t => T t + σ • antilinearMat (γ t)) := by
  sorry

end CauchyRiemannIndex
