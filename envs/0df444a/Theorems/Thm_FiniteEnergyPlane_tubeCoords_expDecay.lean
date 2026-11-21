-- Prove2me | Theorems.Thm_FiniteEnergyPlane_tubeCoords_expDecay
-- name    : FiniteEnergyPlane.tubeCoords_expDecay
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-20T09:44:51.868569+00:00
-- url     : https://prove2.me/theorems/6c8e4509-ec45-400e-b612-526285c14c0c
-- title:
--   Asymptotics of a holomorphic graph over a plane in a standard tube
-- statement:
--   Setting: $S = H^{-1}(1) \subset \mathbb{R}^4$ strictly star-shaped with compatible $J$ on $\xi$, $P = (x, T)$ a periodic Reeb orbit, $\pi$ the radial projection to $S$, $a$ the symplectization coordinate, and $z = e^{2\pi(s+it)}$ the cylindrical coordinate at $\infty$. Let $u : \mathbb{C} \to \mathbb{R}^4 \setminus \{0\}$, $N : \mathbb{C} \to \mathrm{Hom}_{\mathbb{R}}(\mathbb{C}, \mathbb{R}^4)$ be smooth with $(\Delta,\nu) \mapsto Du(z)\Delta + N(z)\nu$ injective, $M$ a unitary frame of $\xi$ along $P$, and assume $a(u) - Ts - d$, $\pi(u) - x(Tt)$ and $e^{-2(Ts+d)}N(e^{2\pi(s+it)})\nu - M(t)\nu$ decay like $e^{-bs}$ in $C^\infty$ ($b > 0$). Let $\Phi(z,w) = u(z) + N(z)w$ be nonvanishing with injective derivative on $\mathbb{C} \times B(0,\rho)$ and satisfy there the weighted two-point lower bound
--   $$c\Big(\frac{|z-z'|}{1+|z|+|z'|} + |w-w'|\Big) \le |a(\Phi(z,w)) - a(\Phi(z',w'))| + |\pi(\Phi(z,w)) - \pi(\Phi(z',w'))|.$$
--   Let $\bar J$ be a standard tube structure of width $\rho$ (a smooth almost complex structure on $\mathbb{C} \times B(0,\rho)$, equal to $i \oplus i$ along $w = 0$, converging exponentially in $C^\infty$ in cylindrical coordinates to a $t$-periodic limit). Assume $|w| \le C_0(\mathrm{dist}(\pi(u(\zeta)+N(\zeta)w), P) + \mathrm{dist}(\pi(u(\zeta)), P))$ for $|\zeta| \ge R_0$, $|w| \le r_0$. Let $\delta < 0$ and suppose $\mathrm{dist}(\pi(u(z)), P) \le C(1+|z|)^{\mu/2\pi}$ for some $\mu < \delta$.
--
--   Let $f$ be a map with $a(f) - Ts - d_f$ and $\pi(f) - x(Tt + c_f)$ decaying like $e^{-b_f s}$ in $C^\infty$ ($b_f > 0$), with $\mathrm{dist}(\pi(f(z)), P) \le C(1+|z|)^{\mu'/2\pi}$ for some $\mu' < \delta$, and suppose $f = \Phi(\psi, v)$ where $\psi$ is a homeomorphism of $\mathbb{C}$, smooth with smooth inverse, $v$ is smooth with $|v| \le \min(\rho/2, r_0)$, $\|D\psi - \mathrm{id}\| \le 1/2$, $(1+|z|)\|Dv(z)\| \le 1$, and $(\psi, v)$ is $\bar J$-holomorphic: $D(\psi,v)\circ i = \bar J(\psi,v)\,D(\psi,v)$.
--
--   Then there are $\kappa \in \mathbb{C} \setminus \{0\}$ and $b' > 0$ such that, in the coordinates $z = e^{2\pi(s+it)}$, $\psi(z)/z - \kappa$ decays like $e^{-b's}$ in $C^\infty$ and $v(z)$ decays like $e^{\delta s}$ in $C^\infty$.
--
--   Role: asymptotics of a pseudoholomorphic graph over a fast plane inside a standard tube; the constant $\kappa$ and the decay of the normal coordinate are what is needed to compare two such graphs at the puncture.
--
--   Formalization note: $\mathbb{R}^4$ is `V 1`; `ExpDecayCInfty f b` means $C^\infty$ decay like $e^{-bs}$ along `cylInf`; `IsStdTubeStructure ρ b₁ Jbar Jinf Sinf` is the standard tube structure; `endA`, `endW` are $a$, $\pi$ along the end; the hypotheses $\mathrm{hH}, \mathrm{hJ}$ fix the setting.
-- source:
--   Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), Section 6

import Definitions.Def_FiniteEnergyPlane_TubeFamily

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Asymptotics of a holomorphic graph in a standard tube. In the setting of a smooth
nonvanishing plane `u` with normal map `N`, unitary frame `M` of `ξ` along `P` and the
exponential decay hypotheses `ha`, `hw`, `hNM` (rate `b > 0`), let `Φ(z, w) = u z + N z w` satisfy
`hΦ`, `hlow` on `ℂ × ball 0 ρ`, let `Jbar` be a standard tube structure of width `ρ`, and let the
normal coordinate be controlled by the distance to `P` as in `hnorm`. Let `δ < 0`, and let `u` and
a map `f` (with exponential asymptotics `hfa`, `hfw` at `P`) approach `P` like `(1 + |z|)^{μ/2π}`
for some `μ < δ`. Suppose `f = Φ(ψ, v)` with `ψ` a homeomorphism of `ℂ`, smooth with smooth inverse,
`v` smooth with `‖v‖ ≤ min (ρ/2) r₀`, `‖Dψ - id‖ ≤ 1/2`, `(1 + ‖z‖) ‖Dv‖ ≤ 1`, and `(ψ, v)`
`Jbar`-holomorphic. Then in the coordinates `z = e^{2π(s+it)}`, `ψ(z)/z - κ` decays like `e^{-b's}`
in `C^∞` for some `κ ≠ 0` and `b' > 0`, and `v` decays like `e^{δ s}` in `C^∞`. -/
theorem tubeCoords_expDecay (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1) (hu : ContDiff ℝ ∞ u)
    (hu0 : ∀ z, u z ≠ 0) (d b : ℝ) (hb : 0 < b)
    (ha : ExpDecayCInfty (fun p : ℝ × ℝ => endA H u cylInf p - P.T * p.1 - d) b)
    (hw : ExpDecayCInfty (fun p : ℝ × ℝ => endW H u cylInf p - P.x (P.T * p.2)) b)
    (N : ℂ → ℂ →L[ℝ] V 1) (hN : ContDiff ℝ ∞ N)
    (hNinj : ∀ (z Δ ν : ℂ), fderiv ℝ u z Δ + N z ν = 0 → Δ = 0 ∧ ν = 0)
    (M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1) (hM : IsUnitaryXiFrame J P M)
    (hNM : ∀ ν : ℂ, ExpDecayCInfty (fun p : ℝ × ℝ =>
      Real.exp (-(2 * (P.T * p.1 + d))) • N (cylInf p.1 p.2) ν - M p.2 (cToVec ν)) b)
    (ρ c : ℝ) (hρ : 0 < ρ) (hc : 0 < c)
    (hΦ : ∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ, u p.1 + N p.1 p.2 ≠ 0 ∧
      Function.Injective (fderiv ℝ (fun q : ℂ × ℂ => u q.1 + N q.1 q.2) p))
    (hlow : ∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ, ∀ q ∈ Set.univ ×ˢ ball (0 : ℂ) ρ,
      c * (‖p.1 - q.1‖ / (1 + ‖p.1‖ + ‖q.1‖) + ‖p.2 - q.2‖) ≤
        |aCoord H (u p.1 + N p.1 p.2) - aCoord H (u q.1 + N q.1 q.2)| +
          ‖proj H (u p.1 + N p.1 p.2) - proj H (u q.1 + N q.1 q.2)‖)
    (b₁ : ℝ) (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (hstd : IsStdTubeStructure ρ b₁ Jbar Jinf Sinf)
    (r₀ C₀ R₀ : ℝ)
    (hnorm : ∀ ζ w : ℂ, R₀ ≤ ‖ζ‖ → ‖w‖ ≤ r₀ →
      ‖w‖ ≤ C₀ * (infDist (proj H (u ζ + N ζ w)) (Set.range P.x) +
        infDist (proj H (u ζ)) (Set.range P.x)))
    (δ : ℝ) (hδ : δ < 0)
    (hδu : ∃ μ < δ, ∃ C : ℝ, ∀ z : ℂ, infDist (proj H (u z)) (Set.range P.x) ≤
      C * (1 + ‖z‖) ^ (μ / (2 * π)))
    (f : ℂ → V 1) (df cf bf : ℝ) (hbf : 0 < bf)
    (hfa : ExpDecayCInfty (fun p : ℝ × ℝ => endA H f cylInf p - P.T * p.1 - df) bf)
    (hfw : ExpDecayCInfty (fun p : ℝ × ℝ => endW H f cylInf p - P.x (P.T * p.2 + cf)) bf)
    (hδf : ∃ μ < δ, ∃ C : ℝ, ∀ z : ℂ, infDist (proj H (f z)) (Set.range P.x) ≤
      C * (1 + ‖z‖) ^ (μ / (2 * π)))
    (ψ : ℂ ≃ₜ ℂ) (v : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hψs : ContDiff ℝ ∞ ψ.symm)
    (hv : ContDiff ℝ ∞ v) (hvρ : ∀ z, ‖v z‖ ≤ ρ / 2) (hvr : ∀ z, ‖v z‖ ≤ r₀)
    (hf : ∀ z, f z = u (ψ z) + N (ψ z) (v z))
    (hDψ : ∀ z, ‖fderiv ℝ ψ z - ContinuousLinearMap.id ℝ ℂ‖ ≤ 1 / 2)
    (hDv : ∀ z, (1 + ‖z‖) * ‖fderiv ℝ v z‖ ≤ 1)
    (hhol : ∀ z, (fderiv ℝ (fun x : ℂ => (ψ x, v x)) z).comp
        (Complex.I • ContinuousLinearMap.id ℝ ℂ) =
      (Jbar (ψ z, v z)).comp (fderiv ℝ (fun x : ℂ => (ψ x, v x)) z)) :
    ∃ (κ : ℂ) (b' : ℝ), κ ≠ 0 ∧ 0 < b' ∧
      ExpDecayCInfty (fun p : ℝ × ℝ => ψ (cylInf p.1 p.2) / cylInf p.1 p.2 - κ) b' ∧
      ExpDecayCInfty (fun p : ℝ × ℝ => v (cylInf p.1 p.2)) (-δ) := by
  sorry

end FiniteEnergyPlane
