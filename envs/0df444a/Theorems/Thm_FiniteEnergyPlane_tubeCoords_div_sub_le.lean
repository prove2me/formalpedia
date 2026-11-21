-- Prove2me | Theorems.Thm_FiniteEnergyPlane_tubeCoords_div_sub_le
-- name    : FiniteEnergyPlane.tubeCoords_div_sub_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-20T18:07:08.67318+00:00
-- url     : https://prove2.me/theorems/f0038a3a-0695-490a-8342-3de0ab9a6f45
-- title:
--   Exponential convergence of the tangential tube coordinate
-- statement:
--   Let $P$ be a Reeb orbit of period $T$, and let $u, f:\mathbb{C}\to V$ have exponential asymptotics at $P$: in the coordinates $z=e^{2\pi(s+it)}$, $\mathrm{endA}(u) - Ts - d$ and $\mathrm{endW}(u) - x(Tt)$ decay like $e^{-bs}$ in $C^\infty$, and $\mathrm{endA}(f) - Ts - d_f$ and $\mathrm{endW}(f) - x(Tt + c_f)$ decay like $e^{-b_f s}$, with $b, b_f > 0$. Let $N:\mathbb{C}\to\mathcal{L}(\mathbb{C},V)$, $\rho, c>0$, and suppose $\Phi(z,w) = u(z)+N(z)w$ satisfies on $\mathbb{C}\times B(0,\rho)$ the weighted lower bound
--   $$c\Big(\frac{|z-z'|}{1+|z|+|z'|} + |w-w'|\Big) \le |\mathrm{aCoord}\,\Phi(z,w) - \mathrm{aCoord}\,\Phi(z',w')| + \|\mathrm{proj}\,\Phi(z,w) - \mathrm{proj}\,\Phi(z',w')\|.$$
--   Let $\psi, v:\mathbb{C}\to\mathbb{C}$ with $\psi$ differentiable, $\|D\psi - \mathrm{id}\|\le 1/2$, $|v|\le \rho/2$ and $f = \Phi(\psi, v)$.
--
--   Then there are $\kappa\ne0$, $\beta>0$, $C$ and $s_1$ with
--   $$\Big|\frac{\psi(e^{2\pi(s+it)})}{e^{2\pi(s+it)}} - \kappa\Big| \le C e^{-\beta s}\qquad (s\ge s_1,\ t\in\mathbb{R}).$$
--
--   Role: $C^0$ asymptotics of the tangential tube coordinate of a map close to a reference end.
--
--   Formalization note: `cylInf s t = exp(2πs)·exp(2πit)`; `ExpDecayCInfty F b` is exponential $C^\infty$ decay of $F(s,t)$ at rate $b$ as $s\to\infty$.
-- source:
--   Toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076, Section 6

import Definitions.Def_FiniteEnergyPlane_TubeFamily

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal Real

/-- The tangential tube coordinate is asymptotically linear. Let `u` and `f` have exponential
asymptotics at `P` (`ha`, `hw`, `hfa`, `hfw`), let `Φ(z, w) = u z + N z w` satisfy the weighted
lower bound `hlow` on `ℂ × ball 0 ρ`, and let `f = Φ(ψ, v)` with `‖v‖ ≤ ρ/2` and
`‖Dψ - id‖ ≤ 1/2`. Then `ψ(z)/z → κ` for some `κ ≠ 0` like `e^{-βs}` in the coordinates
`z = e^{2π(s+it)}`, for some `β > 0`. -/
theorem tubeCoords_div_sub_le (H : V 1 → ℝ) (P : ReebOrbit H) (u : ℂ → V 1) (d b : ℝ)
    (hb : 0 < b)
    (ha : ExpDecayCInfty (fun p : ℝ × ℝ => endA H u cylInf p - P.T * p.1 - d) b)
    (hw : ExpDecayCInfty (fun p : ℝ × ℝ => endW H u cylInf p - P.x (P.T * p.2)) b)
    (N : ℂ → ℂ →L[ℝ] V 1) (ρ c : ℝ) (hρ : 0 < ρ) (hc : 0 < c)
    (hlow : ∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ, ∀ q ∈ Set.univ ×ˢ ball (0 : ℂ) ρ,
      c * (‖p.1 - q.1‖ / (1 + ‖p.1‖ + ‖q.1‖) + ‖p.2 - q.2‖) ≤
        |aCoord H (u p.1 + N p.1 p.2) - aCoord H (u q.1 + N q.1 q.2)| +
          ‖proj H (u p.1 + N p.1 p.2) - proj H (u q.1 + N q.1 q.2)‖)
    (f : ℂ → V 1) (df cf bf : ℝ) (hbf : 0 < bf)
    (hfa : ExpDecayCInfty (fun p : ℝ × ℝ => endA H f cylInf p - P.T * p.1 - df) bf)
    (hfw : ExpDecayCInfty (fun p : ℝ × ℝ => endW H f cylInf p - P.x (P.T * p.2 + cf)) bf)
    (ψ v : ℂ → ℂ) (hψ : Differentiable ℝ ψ) (hvρ : ∀ z, ‖v z‖ ≤ ρ / 2)
    (hf : ∀ z, f z = u (ψ z) + N (ψ z) (v z))
    (hDψ : ∀ z, ‖fderiv ℝ ψ z - ContinuousLinearMap.id ℝ ℂ‖ ≤ 1 / 2) :
    ∃ κ : ℂ, κ ≠ 0 ∧ ∃ β > 0, ∃ C s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ,
      ‖ψ (cylInf s t) / cylInf s t - κ‖ ≤ C * Real.exp (-(β * s)) := by
  sorry

end FiniteEnergyPlane
