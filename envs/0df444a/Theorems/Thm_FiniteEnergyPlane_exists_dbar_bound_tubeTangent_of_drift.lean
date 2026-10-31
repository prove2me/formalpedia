-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_dbar_bound_tubeTangent_of_drift
-- name    : FiniteEnergyPlane.exists_dbar_bound_tubeTangent_of_drift
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-30T10:56:19.462623+00:00
-- url     : https://prove2.me/theorems/252e7625-249d-44e8-ad13-4fee7c24f493
-- title:
--   Tangential Cauchy–Riemann defect of an end in tube coordinates with a drifting phase
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be a strictly star-shaped level with contact planes $\xi$, $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$, $u$ a finite-energy $\tilde J$-holomorphic curve on $D\setminus\{0\}$, $P=(x,T)$ a periodic Reeb orbit and $\varepsilon=\pm1$. In the cylindrical coordinates $e^{-2\pi(s+it)}$ at $0$ write $a(s,t)$ for the symplectization coordinate and $w(s,t)\in S$ for the radial projection of $u$. Suppose that for $s\ge s_0$ $$w(s,t)=\mathrm{proj}\big(x(\tau(s,t))+h(s,t)\big),\qquad h(s,t)\in\xi_{x(\tau(s,t))},$$ with $\tau(s,t+1)=\tau(s,t)+\varepsilon T$ and $h(s,t+1)=h(s,t)$, where $\tau(s,t)-\varepsilon Tt$ is smooth for large $s$ and every derivative of order $\ge1$ of $\tau(s,t)-\varepsilon Tt$ tends to $0$ as $s\to+\infty$, uniformly in $t$ (no limit of $\tau-\varepsilon Tt$ itself is assumed), and $h\to0$ in $C^\infty$, uniformly in $t$. Put $f=a-\varepsilon Ts$ and $g=\tau-\varepsilon Tt$. Then there are $K$ and $s_1$ such that for all $s\ge s_1$ and all $t$$$|\partial_sf-\partial_tg|+|\partial_tf+\partial_sg|\le K\big(\|h\|+\|Dh\|\big)(s,t).$$That is, $f+ig$ is holomorphic in $s+it$ up to an error controlled by $h$ and its first derivative. This describes the directions of an end tangent to the trivial cylinder.
--
--   **Formalization Note** `proj H` is the radial projection onto $S$, `IsInXi H x v` means $v\in\xi_x=\ker\lambda_0(x)\cap\ker dH(x)$, and $C^\infty$ convergence is `TendstoZeroCInfty` (smooth on some $(s_0,\infty)\times\mathbb{R}$, every derivative tends to $0$ uniformly in $t$). Derivatives are `iteratedFDeriv ℝ` on $\mathbb{R}\times\mathbb{R}$. $a$ and $w$ are `endA H u cylEnd` and `endW H u cylEnd`; norms on $V=\mathbb{R}^{2n+2}$ are sup norms. Partial derivatives are `fderiv ℝ _ (s, t) (1, 0)` and `fderiv ℝ _ (s, t) (0, 1)`, and $\|Dh\|$ is the operator norm of `fderiv ℝ h (s, t)`.
-- source:
--   H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations I: asymptotics, Ann. Inst. H. Poincaré Anal. Non Linéaire 13 (1996), Theorem 1.3 and Lemmas 2.6–2.7; C. Wendl, Lectures on Symplectic Field Theory (2026 notes), Proposition 6.7.1

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Let `u` be a finite-energy `J̃`-holomorphic curve on `D \ {0}` and `P = (x, T)` a periodic Reeb
orbit. Suppose that, in the cylindrical coordinates `cylEnd` at `0` and for `s ≥ s₀`,
`w = proj H (x(τ) + h)` with `h ∈ ξ_{x(τ)}`, `τ(s, t + 1) = τ(s, t) + εT` and `h` `1`-periodic,
where `τ - εTt` is smooth for large `s` with every derivative of order `≥ 1` tending to `0`
uniformly in `t`, and `h → 0` in `C^∞`. Put `f = a - εTs` and `g = τ - εTt`. Then `f + i g` is
holomorphic in `s + it` up to an error controlled by `h`:
`|∂ₛf - ∂ₜg| + |∂ₜf + ∂ₛg| ≤ K (‖h‖ + ‖Dh‖)` for `s ≥ s₁`. -/
theorem exists_dbar_bound_tubeTangent_of_drift {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u) (P : ReebOrbit H)
    (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (τ : ℝ × ℝ → ℝ) (h : ℝ × ℝ → V n) (s₀ : ℝ)
    (hθs : ∃ s₂ : ℝ,
      ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => τ p - ε * P.T * p.2) (Set.Ioi s₂ ×ˢ Set.univ))
    (hθ : ∀ m : ℕ, 1 ≤ m → ∀ η > 0, ∃ s₂ : ℝ, ∀ s ≥ s₂, ∀ t : ℝ,
      ‖iteratedFDeriv ℝ m (fun p : ℝ × ℝ => τ p - ε * P.T * p.2) (s, t)‖ ≤ η)
    (hh : TendstoZeroCInfty h)
    (hrep : ∀ s ≥ s₀, ∀ t : ℝ,
      τ (s, t + 1) = τ (s, t) + ε * P.T ∧ h (s, t + 1) = h (s, t) ∧
        IsInXi H (P.x (τ (s, t))) (h (s, t)) ∧
        endW H u cylEnd (s, t) = proj H (P.x (τ (s, t)) + h (s, t))) :
    ∃ K s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ,
      |fderiv ℝ (fun p : ℝ × ℝ => endA H u cylEnd p - ε * P.T * p.1) (s, t) (1, 0) -
          fderiv ℝ (fun p : ℝ × ℝ => τ p - ε * P.T * p.2) (s, t) (0, 1)| +
        |fderiv ℝ (fun p : ℝ × ℝ => endA H u cylEnd p - ε * P.T * p.1) (s, t) (0, 1) +
          fderiv ℝ (fun p : ℝ × ℝ => τ p - ε * P.T * p.2) (s, t) (1, 0)| ≤
        K * (‖h (s, t)‖ + ‖fderiv ℝ h (s, t)‖) := by
  sorry

end FiniteEnergyPlane
