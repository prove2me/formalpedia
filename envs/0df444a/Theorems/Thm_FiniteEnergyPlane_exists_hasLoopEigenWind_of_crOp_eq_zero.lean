-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_hasLoopEigenWind_of_crOp_eq_zero
-- name    : FiniteEnergyPlane.exists_hasLoopEigenWind_of_crOp_eq_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-06T19:28:51.494322+00:00
-- url     : https://prove2.me/theorems/826b7980-08b3-435c-bc32-d3ea73a21853
-- title:
--   Winding number and growth rate of a solution on a cylindrical end
-- statement:
--   Let $S:\mathbb R\times\mathbb R\to\mathbb R^{2\times 2}$ be smooth on $(s_1,\infty)\times\mathbb R$, $1$-periodic in $t$, and exponentially asymptotic in $C^\infty$ to a smooth symmetric loop $S_\infty$. Let $\zeta$ be a smooth $1$-periodic solution of $\partial_s\zeta+J_0\partial_t\zeta+S\zeta=0$ on $s>s_1$ that does not vanish identically near the end, with $\|\zeta(s,t)\|\le Ce^{\delta_0 s}$. Then there are $\mu\le\delta_0$, $k\in\mathbb Z$, and constants $s_2,E$ with $E\ge 0$ such that $\mu$ is an eigenvalue of $S_\infty$ of winding $k$ and, for every $s\ge s_2$, the loop $t\mapsto\zeta(s,t)$ has winding number $k$ and $\|\zeta(s,t)\|\le Ee^{\mu s}$.
--
--   This records the winding number and the exact growth rate of a solution on a cylindrical end in terms of the asymptotic operator.
--
--   Formalization Note: the equation is `CauchyRiemannIndex.crOp S ζ = 0`; winding numbers use `vecToC`, which identifies $\mathbb R^2$ with $\mathbb C$; `HasLoopEigenWind Sinf μ k` says that $\mu$ is an eigenvalue and all its eigenfunctions have winding $k$.
-- source:
--   Hofer-Wysocki-Zehnder, Properties of pseudoholomorphic curves in symplectisations I (1996), asymptotic behaviour of solutions on half-cylinders

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open scoped ContDiff

/-- Let `ζ` be a `1`-periodic solution of `∂ₛζ + J₀ ∂ₜζ + S ζ = 0` on a half-cylinder `s > s₁`, not
vanishing identically near the end, with `‖ζ(s, t)‖ ≤ C e^{δ₀ s}`, where `S` is exponentially
asymptotic to a symmetric loop `S∞`. Then there are `μ ≤ δ₀` and `k` such that `S∞` has eigenvalue
`μ` of winding `k`, and for all large `s` the loop `ζ(s, ·)` has winding number `k` and
`‖ζ(s, t)‖ ≤ E e^{μ s}`. -/
theorem exists_hasLoopEigenWind_of_crOp_eq_zero (s₁ : ℝ) (S : ℝ × ℝ → CauchyRiemannIndex.Mat 1)
    (hS : ∀ i j, ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => S p i j) (Set.Ioi s₁ ×ˢ Set.univ))
    (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (d : ℝ) (hd : 0 < d) (hSas : IsExpAsymptoticTo S Sinf d)
    (ζ : ℝ × ℝ → CauchyRiemannIndex.Vec 1) (hζ : ContDiffOn ℝ ∞ ζ (Set.Ioi s₁ ×ˢ Set.univ))
    (hper : ∀ s > s₁, ∀ t : ℝ, S (s, t + 1) = S (s, t) ∧ ζ (s, t + 1) = ζ (s, t))
    (heq : ∀ s > s₁, ∀ t : ℝ, CauchyRiemannIndex.crOp S ζ (s, t) = 0)
    (hne : ∀ s₀ : ℝ, ∃ s ≥ s₀, ∃ t : ℝ, ζ (s, t) ≠ 0)
    (C δ₀ : ℝ) (hgrowth : ∀ s > s₁, ∀ t : ℝ, ‖ζ (s, t)‖ ≤ C * Real.exp (δ₀ * s)) :
    ∃ (μ : ℝ) (k : ℤ) (s₂ E : ℝ), μ ≤ δ₀ ∧ HasLoopEigenWind Sinf μ k ∧ 0 ≤ E ∧
      ∀ s ≥ s₂, HasLoopWind (fun t => vecToC (ζ (s, t))) k ∧
        ∀ t, ‖ζ (s, t)‖ ≤ E * Real.exp (μ * s) := by
  sorry

end FiniteEnergyPlane
