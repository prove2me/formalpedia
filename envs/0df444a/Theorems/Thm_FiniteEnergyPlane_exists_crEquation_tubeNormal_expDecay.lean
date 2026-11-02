-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_crEquation_tubeNormal_expDecay
-- name    : FiniteEnergyPlane.exists_crEquation_tubeNormal_expDecay
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-01T09:05:28.174673+00:00
-- url     : https://prove2.me/theorems/30949542-3f7f-4361-bf45-05248086671d
-- title:
--   Linear Cauchy–Riemann equation with exponentially convergent coefficients for the normal part of an end
-- statement:
--   Let $u$ be a finite-energy $\tilde J$-holomorphic curve on $D\setminus\{0\}$, $P=(x,T)$ a periodic Reeb orbit, $Z$ a unitary frame of $\xi$ along $P$ in which the asymptotic operator is $A_P(Z\eta)=Z(-J_0\eta'-S_\infty\eta)$ with $S_\infty$ a smooth symmetric loop, $\varepsilon=\pm1$, and suppose the end $w(s,t)$ of $u$ at $0$ is written for $s\ge s_0$ as $w=\mathrm{proj}(x(\tau)+h)$, $h\in\xi_{x(\tau)}$, $\tau(s,t+1)=\tau(s,t)+\varepsilon T$, $h$ $1$-periodic, with $\tau-\varepsilon Tt-c\to0$ and $h\to0$ in $C^\infty$, and with $$|\tau(s,t)-\varepsilon Tt-c|+\|h(s,t)\|\le C_0e^{-bs},\qquad b>0.$$Then there are $s_1$, $d>0$, $C$ and maps $S$ (matrix valued) and $\zeta$, smooth on $(s_1,\infty)\times\mathbb{R}$, such that $S(s,t)-\varepsilon S_\infty(\varepsilon t+c/T)$ decays like $e^{-ds}$ in $C^\infty$, and for $s>s_1$: $S$, $\zeta$ are $1$-periodic in $t$, $\partial_s\zeta+J_0\partial_t\zeta+S\zeta=0$, $h=Z(\tau/T)\zeta$ and $\|\zeta(s,t)\|\le Ce^{-ds}$.
--
--   This turns the normal part of an exponentially convergent end into a solution of a linear Cauchy–Riemann equation whose coefficients converge exponentially.
--
--   **Formalization Note** Exponential $C^\infty$ convergence is `IsExpAsymptoticTo` (entrywise `ExpDecayCInfty`); the operator is `CauchyRiemannIndex.crOp`; the hypothesis on $Z$, $S_\infty$ is the identity `hZS` for every smooth $1$-periodic $\eta$.
-- source:
--   Used for U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Theorem 2.11 and Lemma 2.12; H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations I: asymptotics, Ann. Inst. H. Poincaré Anal. Non Linéaire 13 (1996)

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Linear Cauchy–Riemann equation for the normal component of an end in tube coordinates, with
exponentially convergent coefficients. Let `u` be a finite-energy curve on `D \ {0}`, `P` a Reeb
orbit, `Z` a unitary frame of `ξ` along `P` in which `A_P` is `-J₀ ∂ₜ - S∞`, and suppose the end
is written as `w = proj H (x(τ) + h)`, `h ∈ ξ_{x(τ)}`, with `τ - εTt - c → 0` and `h → 0` in `C^∞`
and with `|τ - εTt - c| + ‖h‖ ≤ C₀ e^{-bs}`, `b > 0`. Then for some `s₁` and `d > 0` there are
`S` and `ζ`, smooth and `1`-periodic on `s > s₁`, with `h = Z(τ/T) ζ`, `∂ₛζ + J₀ ∂ₜζ + S ζ = 0`,
`‖ζ(s, t)‖ ≤ C e^{-ds}` for all `s > s₁`, and `S(s, t) - ε S∞(εt + c/T)` decaying like `e^{-ds}`
in `C^∞`. -/
theorem exists_crEquation_tubeNormal_expDecay {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u) (P : ReebOrbit H)
    (Z : ℝ → CauchyRiemannIndex.Vec n →L[ℝ] V n) (hZ : IsUnitaryXiFrame J P Z)
    (Sinf : ℝ → CauchyRiemannIndex.Mat n) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (hZS : ∀ η : ℝ → CauchyRiemannIndex.Vec n, ContDiff ℝ ∞ η → Function.Periodic η 1 →
      ∀ t : ℝ, asympOp J P (fun t => Z t (η t)) t =
        Z t (-(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ n) (deriv η t)) -
          Matrix.toEuclideanLin (Sinf t) (η t)))
    (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (c : ℝ) (τ : ℝ × ℝ → ℝ) (h : ℝ × ℝ → V n) (s₀ : ℝ)
    (hτ : TendstoZeroCInfty (fun p : ℝ × ℝ => τ p - ε * P.T * p.2 - c))
    (hh : TendstoZeroCInfty h)
    (hrep : ∀ s ≥ s₀, ∀ t : ℝ,
      τ (s, t + 1) = τ (s, t) + ε * P.T ∧ h (s, t + 1) = h (s, t) ∧
        IsInXi H (P.x (τ (s, t))) (h (s, t)) ∧
        endW H u cylEnd (s, t) = proj H (P.x (τ (s, t)) + h (s, t)))
    (b C₀ : ℝ) (hb : 0 < b)
    (hdec : ∀ s ≥ s₀, ∀ t : ℝ,
      |τ (s, t) - ε * P.T * t - c| + ‖h (s, t)‖ ≤ C₀ * Real.exp (-(b * s))) :
    ∃ (s₁ d C : ℝ) (S : ℝ × ℝ → CauchyRiemannIndex.Mat n) (ζ : ℝ × ℝ → CauchyRiemannIndex.Vec n),
      0 < d ∧
      (∀ i j, ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => S p i j) (Set.Ioi s₁ ×ˢ Set.univ)) ∧
      IsExpAsymptoticTo S (fun t => ε • Sinf (ε * t + c / P.T)) d ∧
      ContDiffOn ℝ ∞ ζ (Set.Ioi s₁ ×ˢ Set.univ) ∧
      ∀ s > s₁, ∀ t : ℝ, S (s, t + 1) = S (s, t) ∧ ζ (s, t + 1) = ζ (s, t) ∧
        CauchyRiemannIndex.crOp S ζ (s, t) = 0 ∧ h (s, t) = Z (τ (s, t) / P.T) (ζ (s, t)) ∧
        ‖ζ (s, t)‖ ≤ C * Real.exp (-(d * s)) := by
  sorry

end FiniteEnergyPlane
