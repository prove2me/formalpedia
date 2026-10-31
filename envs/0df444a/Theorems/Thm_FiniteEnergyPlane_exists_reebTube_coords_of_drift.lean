-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_reebTube_coords_of_drift
-- name    : FiniteEnergyPlane.exists_reebTube_coords_of_drift
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-30T10:56:19.048163+00:00
-- url     : https://prove2.me/theorems/eb814c04-2adb-4c99-814a-059d67b9114f
-- title:
--   Tube coordinates near a periodic Reeb orbit for maps converging up to a drifting phase
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be a strictly star-shaped level with contact planes $\xi_x=\ker\lambda_0(x)\cap\ker dH(x)$, $P=(x,T)$ a periodic Reeb orbit on $S$ and $\varepsilon=\pm1$. Let $w:\mathbb{R}^2\to\mathbb{R}^{2n+2}$ be smooth on $(s_0,\infty)\times\mathbb{R}$, take values in $S$ for $s>s_0$, be $1$-periodic in $t$, and suppose that for every $m\ge0$ and $\eta>0$ there is $s_1$ such that for every $s\ge s_1$ some $c'\in\mathbb{R}$ satisfies $\|D^j\big(w-x(\varepsilon T\,\cdot_2+c')\big)(s,t)\|\le\eta$ for all $t$ and all $j\le m$. Then there are functions $\tau$, $h$ and constants $s_1$, $K$ such that
--
--   - $\tau(s,t)-\varepsilon Tt$ is smooth for large $s$, and each of its derivatives of order $\ge1$ tends to $0$ as $s\to+\infty$, uniformly in $t$;
--   - $h\to0$ in $C^\infty$, uniformly in $t$;
--   - for all $s\ge s_1$ and all $t$: $\tau(s,t+1)=\tau(s,t)+\varepsilon T$, $h(s,t+1)=h(s,t)$, $h(s,t)\in\xi_{x(\tau(s,t))}$, $w(s,t)=\mathrm{proj}\big(x(\tau(s,t))+h(s,t)\big)$ and $\|w(s,t)-x(\tau(s,t))\|\le K\|h(s,t)\|$.
--
--   These are tube coordinates $(\tau,h)$ (position along the orbit, normal component) for a map that approaches the orbit only up to an $s$-dependent phase, as happens for an end of a finite-energy curve before one knows that the phase converges.
--
--   **Formalization Note** `proj H` is the radial projection onto $S$, `IsInXi H x v` means $v\in\xi_x$, derivatives are `iteratedFDeriv ℝ` on $\mathbb{R}\times\mathbb{R}$, $x(\varepsilon T\,\cdot_2+c')$ is the map $(s,t)\mapsto x(\varepsilon Tt+c')$, and $C^\infty$ convergence is `TendstoZeroCInfty` (smooth on some $(s_0,\infty)\times\mathbb{R}$, every derivative tends to $0$ uniformly in $t$). Norms on $V=\mathbb{R}^{2n+2}$ are sup norms.
-- source:
--   H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations I: asymptotics, Ann. Inst. H. Poincaré Anal. Non Linéaire 13 (1996), Theorem 1.3 and Lemmas 2.6–2.7; C. Wendl, Lectures on Symplectic Field Theory (2026 notes), Proposition 6.7.1

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Tube coordinates around a periodic Reeb orbit `P = (x, T)` on a strictly star-shaped level `S`,
for maps that approach the orbit up to an `s`-dependent phase. Let `w(s, t) ∈ S` (for `s > s₀`) be
smooth on `(s₀, ∞) × ℝ` and `1`-periodic in `t`, and suppose that for every `m` and `η > 0`, for
all large `s` there is a phase `c'` with the derivatives of order `≤ m` of `w - x(εTt + c')` at
`(s, t)` at most `η` for all `t`. Then for `s ≥ s₁` the map `w` is written as
`w = proj H (x(τ) + h)` with `h ∈ ξ_{x(τ)}`, where `τ(s, t + 1) = τ(s, t) + εT`, `h` is
`1`-periodic, `τ - εTt` is smooth for large `s` with every derivative of order `≥ 1` tending to `0`
uniformly in `t`, `h → 0` in `C^∞`, and `‖w - x(τ)‖ ≤ K ‖h‖`. -/
theorem exists_reebTube_coords_of_drift {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (P : ReebOrbit H) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (w : ℝ × ℝ → V n) (s₀ : ℝ)
    (hwsm : ContDiffOn ℝ ∞ w (Set.Ioi s₀ ×ˢ Set.univ))
    (hwS : ∀ s > s₀, ∀ t : ℝ, H (w (s, t)) = 1)
    (hwper : ∀ s t : ℝ, w (s, t + 1) = w (s, t))
    (hw : ∀ m : ℕ, ∀ η > 0, ∃ s₁ : ℝ, ∀ s ≥ s₁, ∃ c' : ℝ, ∀ j ≤ m, ∀ t : ℝ,
      ‖iteratedFDeriv ℝ j (fun p : ℝ × ℝ => w p - P.x (ε * P.T * p.2 + c')) (s, t)‖ ≤ η) :
    ∃ (τ : ℝ × ℝ → ℝ) (h : ℝ × ℝ → V n) (s₁ K : ℝ),
      (∃ s₂ : ℝ, ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => τ p - ε * P.T * p.2) (Set.Ioi s₂ ×ˢ Set.univ)) ∧
      (∀ m : ℕ, 1 ≤ m → ∀ η > 0, ∃ s₂ : ℝ, ∀ s ≥ s₂, ∀ t : ℝ,
        ‖iteratedFDeriv ℝ m (fun p : ℝ × ℝ => τ p - ε * P.T * p.2) (s, t)‖ ≤ η) ∧
      TendstoZeroCInfty h ∧
      ∀ s ≥ s₁, ∀ t : ℝ,
        τ (s, t + 1) = τ (s, t) + ε * P.T ∧ h (s, t + 1) = h (s, t) ∧
        IsInXi H (P.x (τ (s, t))) (h (s, t)) ∧ w (s, t) = proj H (P.x (τ (s, t)) + h (s, t)) ∧
        ‖w (s, t) - P.x (τ (s, t))‖ ≤ K * ‖h (s, t)‖ := by
  sorry

end FiniteEnergyPlane
