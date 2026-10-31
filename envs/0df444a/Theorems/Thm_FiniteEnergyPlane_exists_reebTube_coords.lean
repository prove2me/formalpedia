-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_reebTube_coords
-- name    : FiniteEnergyPlane.exists_reebTube_coords
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-29T21:31:57.687397+00:00
-- url     : https://prove2.me/theorems/8f60b548-aba4-4165-a8aa-c902c057c5dc
-- title:
--   Tube coordinates near a periodic Reeb orbit on a star-shaped level
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be a strictly star-shaped level with contact planes $\xi_x=\ker\lambda_0(x)\cap\ker dH(x)$, $P=(x,T)$ a periodic Reeb orbit on $S$, $\varepsilon=\pm1$ and $c\in\mathbb{R}$. Let $w:\mathbb{R}^2\to\mathbb{R}^{2n+2}$ take values in $S$ for $s>s_0$, be $1$-periodic in $t$, and satisfy $w(s,t)-x(\varepsilon Tt+c)\to0$ in $C^\infty$, uniformly in $t$, as $s\to+\infty$. Then there are functions $\tau$, $h$ and constants $s_1$, $K$ such that $\tau(s,t)-\varepsilon Tt-c\to0$ and $h\to0$ in $C^\infty$, and for all $s\ge s_1$ and all $t$:
--
--   - $\tau(s,t+1)=\tau(s,t)+\varepsilon T$ and $h(s,t+1)=h(s,t)$;
--   - $h(s,t)\in\xi_{x(\tau(s,t))}$ and $w(s,t)=\mathrm{proj}\big(x(\tau(s,t))+h(s,t)\big)$;
--   - $\|w(s,t)-x(\tau(s,t))\|\le K\|h(s,t)\|$ and $\|w(s,t)-x(\varepsilon Tt+c)\|\le K\big(\|h(s,t)\|+|\tau(s,t)-\varepsilon Tt-c|\big)$.
--
--   These are the tube coordinates $(\tau,h)$ in which the asymptotic behaviour of a finite-energy curve near a Reeb orbit is described (as in Hryniewicz, Theorem 2.11); $\tau$ is the position along the orbit and $h$ the component normal to it.
--
--   **Formalization Note** `proj H` is the radial projection onto $S$, `IsInXi H x v` means $v\in\xi_x$, and $C^\infty$ convergence is `TendstoZeroCInfty` (smooth on some $(s_0,\infty)\times\mathbb{R}$, every derivative tends to $0$ uniformly in $t$). Norms on $V=\mathbb{R}^{2n+2}$ are sup norms.
-- source:
--   U. Hryniewicz, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Theorem 2.10; H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations I: asymptotics, Ann. Inst. H. Poincaré Anal. Non Linéaire 13 (1996); C. Wendl, Lectures on Symplectic Field Theory (2026 notes), Proposition 6.7.1

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Tube coordinates around a periodic Reeb orbit `P = (x, T)` on a strictly star-shaped level `S`.
Let `w(s, t) ∈ S` (for `s > s₀`) be `1`-periodic in `t` with `w(s, t) - x(εTt + c) → 0` in `C^∞`.
Then for `s ≥ s₁` the map `w` is written as `w = proj H (x(τ) + h)` with `h ∈ ξ_{x(τ)}`, where
`τ(s, t + 1) = τ(s, t) + εT`, `h` is `1`-periodic, `τ(s, t) - εTt - c → 0` and `h → 0` in `C^∞`,
and `‖w - x(τ)‖ ≤ K ‖h‖`, `‖w - x(εTt + c)‖ ≤ K (‖h‖ + |τ - εTt - c|)`. -/
theorem exists_reebTube_coords {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (P : ReebOrbit H) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (c : ℝ) (w : ℝ × ℝ → V n) (s₀ : ℝ)
    (hwS : ∀ s > s₀, ∀ t : ℝ, H (w (s, t)) = 1)
    (hwper : ∀ s t : ℝ, w (s, t + 1) = w (s, t))
    (hw : TendstoZeroCInfty (fun p : ℝ × ℝ => w p - P.x (ε * P.T * p.2 + c))) :
    ∃ (τ : ℝ × ℝ → ℝ) (h : ℝ × ℝ → V n) (s₁ K : ℝ),
      TendstoZeroCInfty (fun p : ℝ × ℝ => τ p - ε * P.T * p.2 - c) ∧ TendstoZeroCInfty h ∧
      ∀ s ≥ s₁, ∀ t : ℝ,
        τ (s, t + 1) = τ (s, t) + ε * P.T ∧ h (s, t + 1) = h (s, t) ∧
        IsInXi H (P.x (τ (s, t))) (h (s, t)) ∧ w (s, t) = proj H (P.x (τ (s, t)) + h (s, t)) ∧
        ‖w (s, t) - P.x (τ (s, t))‖ ≤ K * ‖h (s, t)‖ ∧
        ‖w (s, t) - P.x (ε * P.T * t + c)‖ ≤ K * (‖h (s, t)‖ + |τ (s, t) - ε * P.T * t - c|) := by
  sorry

end FiniteEnergyPlane
