-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_expDecay_tubeNormal
-- name    : FiniteEnergyPlane.exists_expDecay_tubeNormal
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-29T21:31:56.911704+00:00
-- url     : https://prove2.me/theorems/56946f6b-bb39-4bd6-bf8c-bf77b8533654
-- title:
--   Exponential decay of the normal component of a nondegenerate end in tube coordinates
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be a strictly star-shaped level with contact planes $\xi$, $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$, $u$ a finite-energy $\tilde J$-holomorphic curve on $D\setminus\{0\}$ and $P=(x,T)$ a periodic Reeb orbit, $\varepsilon=\pm1$, $c\in\mathbb{R}$. In the cylindrical coordinates $e^{-2\pi(s+it)}$ at $0$ write $a(s,t)$ for the symplectization coordinate and $w(s,t)\in S$ for the radial projection of $u$. Suppose that for $s\ge s_0$ $$w(s,t)=\mathrm{proj}\big(x(\tau(s,t))+h(s,t)\big),\qquad h(s,t)\in\xi_{x(\tau(s,t))},$$ with $\tau(s,t+1)=\tau(s,t)+\varepsilon T$ and $h(s,t+1)=h(s,t)$, where $\tau(s,t)-\varepsilon Tt-c\to0$ and $h\to0$ in $C^\infty$, uniformly in $t$, as $s\to+\infty$. If $P$ is nondegenerate, then $h$ decays exponentially: there are $\delta>0$, $C$ and $s_1$ with $\|h(s,t)\|\le Ce^{-\delta s}$ for all $s\ge s_1$ and all $t$.
--
--   This is the $C^0$ exponential decay of the normal part of an asymptotically cylindrical end at a nondegenerate orbit (Wendl, Proposition 6.7.1).
--
--   **Formalization Note** `proj H` is the radial projection onto $S$, `IsInXi H x v` means $v\in\xi_x=\ker\lambda_0(x)\cap\ker dH(x)$, and $C^\infty$ convergence is `TendstoZeroCInfty` (smooth on some $(s_0,\infty)\times\mathbb{R}$, every derivative tends to $0$ uniformly in $t$). $a$ and $w$ are `endA H u cylEnd` and `endW H u cylEnd`; norms on $V=\mathbb{R}^{2n+2}$ are sup norms.
-- source:
--   U. Hryniewicz, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Theorem 2.10; H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations I: asymptotics, Ann. Inst. H. Poincaré Anal. Non Linéaire 13 (1996); C. Wendl, Lectures on Symplectic Field Theory (2026 notes), Proposition 6.7.1

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Let `u` be a finite-energy `J̃`-holomorphic curve on `D \ {0}` and `P = (x, T)` a nondegenerate
periodic Reeb orbit. Suppose that, in the cylindrical coordinates `cylEnd` at `0` and for `s ≥ s₀`,
`w = proj H (x(τ) + h)` with `h ∈ ξ_{x(τ)}`, `τ(s, t + 1) = τ(s, t) + εT` and `h` `1`-periodic,
where `τ(s, t) - εTt - c → 0` and `h → 0` in `C^∞`. Then the normal component `h` decays
exponentially: `‖h(s, t)‖ ≤ C e^{-δs}` for some `δ > 0`. -/
theorem exists_expDecay_tubeNormal {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u) (P : ReebOrbit H) (hP : P.IsNondegenerate)
    (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (c : ℝ) (τ : ℝ × ℝ → ℝ) (h : ℝ × ℝ → V n) (s₀ : ℝ)
    (hτ : TendstoZeroCInfty (fun p : ℝ × ℝ => τ p - ε * P.T * p.2 - c))
    (hh : TendstoZeroCInfty h)
    (hrep : ∀ s ≥ s₀, ∀ t : ℝ,
      τ (s, t + 1) = τ (s, t) + ε * P.T ∧ h (s, t + 1) = h (s, t) ∧
        IsInXi H (P.x (τ (s, t))) (h (s, t)) ∧
        endW H u cylEnd (s, t) = proj H (P.x (τ (s, t)) + h (s, t))) :
    ∃ δ > 0, ∃ C s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ, ‖h (s, t)‖ ≤ C * Real.exp (-(δ * s)) := by
  sorry

end FiniteEnergyPlane
