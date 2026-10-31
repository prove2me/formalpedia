-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_crEquation_tubeNormal_of_drift
-- name    : FiniteEnergyPlane.exists_crEquation_tubeNormal_of_drift
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-30T16:17:48.481835+00:00
-- url     : https://prove2.me/theorems/0814eae7-814f-45c1-8ceb-a72da97a71f0
-- title:
--   The normal component of an end with a drifting phase solves a linear Cauchy–Riemann equation
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be a strictly star-shaped level with contact planes $\xi$, $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$, $u$ a finite-energy $\tilde J$-holomorphic curve on $D\setminus\{0\}$, $P=(x,T)$ a periodic Reeb orbit and $\varepsilon=\pm1$. Let $Z(t):\mathbb{R}^{2n}\to\xi_{x(Tt)}$ be a unitary frame along $P$ and $S_\infty$ the smooth loop of symmetric matrices with $A_P(Z\eta)=Z(-J_0\eta'-S_\infty\eta)$ for the asymptotic operator $A_P$. In the cylindrical coordinates $e^{-2\pi(s+it)}$ at $0$ let $w(s,t)\in S$ be the radial projection of $u$, and suppose that for $s\ge s_0$$$w(s,t)=\mathrm{proj}\big(x(\tau(s,t))+h(s,t)\big),\qquad h(s,t)\in\xi_{x(\tau(s,t))},$$ with $\tau(s,t+1)=\tau(s,t)+\varepsilon T$ and $h(s,t+1)=h(s,t)$, where $\theta(s,t)=\tau(s,t)-\varepsilon Tt$ is smooth for large $s$ and every derivative of order $\ge1$ of $\theta$ tends to $0$ uniformly in $t$ as $s\to+\infty$ (no limit of $\theta$ itself is assumed), and $h\to0$ in $C^\infty$. Then there are $s_1$, a matrix-valued $S(s,t)$ and $\zeta(s,t)\in\mathbb{R}^{2n}$ such that $S$ and $\zeta$ are smooth on $(s_1,\infty)\times\mathbb{R}$, $\zeta\to0$ uniformly in $t$, every entry of $S(s,t)-\varepsilon S_\infty(\tau(s,t)/T)$ tends to $0$ in $C^\infty$, and for all $s>s_1$ and all $t$:
--
--   - $S$ and $\zeta$ are $1$-periodic in $t$;
--   - $h(s,t)=Z(\tau(s,t)/T)\,\zeta(s,t)$;
--   - $\partial_s\zeta+J_0\partial_t\zeta+S\zeta=0$.
--
--   So, in a unitary frame, the component of the end normal to the orbit satisfies a linear Cauchy–Riemann equation whose coefficient follows the asymptotic operator of $P$ along the drifting phase $\tau/T$. This extends `exists_crEquation_tubeNormal` (f263e350), where $\tau-\varepsilon Tt$ converges to a constant $c$.
--
--   **Formalization Note** `proj H` is the radial projection onto $S$, `IsInXi H x v` means $v\in\xi_x=\ker\lambda_0(x)\cap\ker dH(x)$, $w$ is `endW H u cylEnd`, the frame is `IsUnitaryXiFrame` and $A_P$ is `asympOp`. $C^\infty$ convergence is `TendstoZeroCInfty` (smooth on some $(s_0,\infty)\times\mathbb{R}$, every derivative tends to $0$ uniformly in $t$), applied entrywise to $S-\varepsilon S_\infty(\tau/T)$; uniform convergence is `TendstoZeroUnif`. `Mat n` and `Vec n` are $2n\times2n$ real matrices and $\mathbb{R}^{2n}$, `crOp S ζ` is $\partial_s\zeta+J_0\partial_t\zeta+S\zeta$, a loop of symmetric matrices is `IsSymLoop` (continuous, $1$-periodic, symmetric), and nondegeneracy of $-J_0\partial_t-S_\infty$ is `CauchyRiemannIndex.IsNondegenerate` ($1$ is not an eigenvalue of the time-$1$ map $\Psi(1)$ of $\Psi'=J_0S_\infty\Psi$, $\Psi(0)=1$).
-- source:
--   H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations I: asymptotics, Ann. Inst. H. Poincaré Anal. Non Linéaire 13 (1996), Section 2; U. Hryniewicz, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Theorem 2.10

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Let `u` be a finite-energy `J̃`-holomorphic curve on `D \ {0}`, `P = (x, T)` a periodic Reeb
orbit, `Z` a unitary frame of `ξ` along `P`, and `S∞` the loop of symmetric matrices representing
the asymptotic operator in this frame, `A_P (Z η) = Z (-J₀ η' - S∞ η)`. Suppose that, in the
cylindrical coordinates `cylEnd` at `0` and for `s ≥ s₀`, `w = proj H (x(τ) + h)` with
`h ∈ ξ_{x(τ)}`, `τ(s, t + 1) = τ(s, t) + εT` and `h` `1`-periodic, where `τ - εTt` is smooth for
large `s` with every derivative of order `≥ 1` tending to `0` uniformly in `t`, and `h → 0` in
`C^∞`. Then, for `s` beyond some `s₁`, the frame coordinates `ζ` of `h`,
`h(s, t) = Z(τ(s, t) / T) ζ(s, t)`, are smooth, `1`-periodic, tend to `0`, and solve a linear
Cauchy–Riemann equation `∂ₛζ + J₀ ∂ₜζ + S ζ = 0` with smooth `1`-periodic coefficient `S` such
that `S(s, t) - ε S∞(τ(s, t) / T) → 0` in `C^∞`. -/
theorem exists_crEquation_tubeNormal_of_drift {n : ℕ} (H : V n → ℝ)
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
    ∃ (s₁ : ℝ) (S : ℝ × ℝ → CauchyRiemannIndex.Mat n) (ζ : ℝ × ℝ → CauchyRiemannIndex.Vec n),
      (∀ i j, ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => S p i j) (Set.Ioi s₁ ×ˢ Set.univ)) ∧
      (∀ i j, TendstoZeroCInfty (fun p : ℝ × ℝ => S p i j - (ε • Sinf (τ p / P.T)) i j)) ∧
      ContDiffOn ℝ ∞ ζ (Set.Ioi s₁ ×ˢ Set.univ) ∧ TendstoZeroUnif ζ ∧
      ∀ s > s₁, ∀ t : ℝ, S (s, t + 1) = S (s, t) ∧ ζ (s, t + 1) = ζ (s, t) ∧
        CauchyRiemannIndex.crOp S ζ (s, t) = 0 ∧ h (s, t) = Z (τ (s, t) / P.T) (ζ (s, t)) := by
  sorry

end FiniteEnergyPlane
