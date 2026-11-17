-- Prove2me | Theorems.Thm_FiniteEnergyPlane_expDecayCInftyTube_cylJ_sub_of_intertwining
-- name    : FiniteEnergyPlane.expDecayCInftyTube_cylJ_sub_of_intertwining
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-16T18:13:57.643032+00:00
-- url     : https://prove2.me/theorems/edd05fe5-2d47-4856-a687-903b412fb89c
-- title:
--   The almost complex structure on a tube converges to its cylindrical limit model
-- statement:
--   Let $S = H^{-1}(1) \subset \mathbb{R}^4$ be a strictly star-shaped level with a compatible complex structure $J$ on $\xi$, $\tilde J$ the induced almost complex structure on $\mathbb{R}^4 \setminus \{0\}$, $P = (x, T)$ a periodic Reeb orbit and $M(t)$ a unitary frame of $\xi$ along $P$. Let $u : \mathbb{C} \to \mathbb{R}^4 \setminus \{0\}$ and $N(z) : \mathbb{C} \to \mathbb{R}^4$ (real linear) be smooth, such that in the coordinates $z = e^{2\pi(s+it)}$ the functions $a(u) - Ts - d$, $\pi(u) - x(Tt)$ and $e^{-2(Ts+d)} N(e^{2\pi(s+it)})\nu - M(t)\nu$ (each $\nu \in \mathbb{C}$) decay like $e^{-bs}$ in $C^\infty$, $b > 0$.
--
--   Put $\Phi(z, w) = u(z) + N(z) w$, $m(t, w) = x(Tt) + M(t) w$, and let $L(t, w)$ be the derivative of $(\zeta, w) \mapsto e^{2T \operatorname{Re}\zeta}\, m(\operatorname{Im}\zeta, w)$ at $(it, w)$. Let $\rho > 0$ and assume:
--   - $m(t, w) \ne 0$ and $L(t, w)$ is injective for $|w| \le \rho$;
--   - $\Phi \ne 0$ and $D\Phi$ is injective on $\mathbb{C} \times B_\rho(0)$;
--   - $D\Phi \circ \bar J = \tilde J(\Phi) \circ D\Phi$ on $\mathbb{C} \times B_\rho(0)$, and $L(t, w) \circ J_\infty(t, w) = \tilde J(m(t, w)) \circ L(t, w)$ for $|w| < \rho$.
--
--   Then $\bar J$ written in the coordinates $(s + it, w)$, i.e. $C(s,t)^{-1} \bar J(e^{2\pi(s+it)}, w)\, C(s,t)$ with $C(s,t)(\sigma, \omega) = (2\pi e^{2\pi(s+it)}\sigma, \omega)$, converges to $J_\infty(t, w)$ like $e^{-bs}$ in $C^\infty$ as $s \to +\infty$, uniformly in $t \in \mathbb{R}$ and $w \in B_\rho(0)$.
--
--   Role: this is the convergence clause of a standard tube structure around a finite-energy plane.
--
--   Formalization note: $\mathbb{R}^4$ is `V 1`, $\tilde J$ is `Jtilde H J`, $a$ and $\pi$ are `aCoord H` and `proj H`; the conjugated structure is `cylJ Jbar s t w` with `cylScale`, `cylScaleInv`; the decay notions are `ExpDecayCInfty` and `ExpDecayCInftyTube`.
-- source:
--   Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), Section 6

import Definitions.Def_FiniteEnergyPlane_TubeFamily
import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Convergence of the tube structure to its limit model. Let `u`, `N`, `M` be as for a standard
tube: `aCoord (u) - T s - d`, `proj (u) - x(T t)` and `e^{-2(Ts+d)} N(e^{2π(s+it)}) ν - M(t) ν`
decay like `e^{-bs}` in `C^∞`. Put `Φ(z, w) = u z + N z w`, `m(t, w) = x(T t) + M(t)(cToVec w)`
and let `L(t, w)` be the derivative of `(ζ, w) ↦ e^{2T Re ζ} m(Im ζ, w)` at `(i t, w)`. Assume
that `m ≠ 0` and `L` is injective for `|w| ≤ ρ`, that `Φ ≠ 0` and `DΦ` is injective on
`ℂ × ball 0 ρ`, and that `DΦ ∘ Jbar = J̃(Φ) ∘ DΦ` on `ℂ × ball 0 ρ` and
`L ∘ Jinf = J̃(m) ∘ L` for `|w| < ρ`. Then `Jbar`, written in the coordinates
`z = e^{2π(s+it)}`, converges to `Jinf` like `e^{-bs}` in `C^∞`, uniformly in `t` and
`w ∈ ball 0 ρ`. -/
theorem expDecayCInftyTube_cylJ_sub_of_intertwining (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1) (hu : ContDiff ℝ ∞ u) (hu0 : ∀ z, u z ≠ 0)
    (d b : ℝ) (hb : 0 < b)
    (ha : ExpDecayCInfty (fun p : ℝ × ℝ => endA H u cylInf p - P.T * p.1 - d) b)
    (hw : ExpDecayCInfty (fun p : ℝ × ℝ => endW H u cylInf p - P.x (P.T * p.2)) b)
    (N : ℂ → ℂ →L[ℝ] V 1) (hN : ContDiff ℝ ∞ N)
    (M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1) (hM : IsUnitaryXiFrame J P M)
    (hNM : ∀ ν : ℂ, ExpDecayCInfty (fun p : ℝ × ℝ =>
      Real.exp (-(2 * (P.T * p.1 + d))) • N (cylInf p.1 p.2) ν - M p.2 (cToVec ν)) b)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hL : ∀ (t : ℝ) (w : ℂ), w ∈ closedBall (0 : ℂ) ρ →
      P.x (P.T * t) + M t (cToVec w) ≠ 0 ∧
      Function.Injective (fderiv ℝ (fun q : ℂ × ℂ => Real.exp (2 * P.T * q.1.re) •
        (P.x (P.T * q.1.im) + M q.1.im (cToVec q.2))) ((t : ℂ) * Complex.I, w)))
    (hΦ : ∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ, u p.1 + N p.1 p.2 ≠ 0 ∧
      Function.Injective (fderiv ℝ (fun q : ℂ × ℂ => u q.1 + N q.1 q.2) p))
    (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (hJbar : ∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ,
      (fderiv ℝ (fun q : ℂ × ℂ => u q.1 + N q.1 q.2) p).comp (Jbar p) =
        (Jtilde H J (u p.1 + N p.1 p.2)).comp
          (fderiv ℝ (fun q : ℂ × ℂ => u q.1 + N q.1 q.2) p))
    (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (hJinf : ∀ (t : ℝ) (w : ℂ), w ∈ ball (0 : ℂ) ρ →
      (fderiv ℝ (fun q : ℂ × ℂ => Real.exp (2 * P.T * q.1.re) •
        (P.x (P.T * q.1.im) + M q.1.im (cToVec q.2))) ((t : ℂ) * Complex.I, w)).comp
          (Jinf (t, w)) =
        (Jtilde H J (P.x (P.T * t) + M t (cToVec w))).comp
          (fderiv ℝ (fun q : ℂ × ℂ => Real.exp (2 * P.T * q.1.re) •
            (P.x (P.T * q.1.im) + M q.1.im (cToVec q.2))) ((t : ℂ) * Complex.I, w))) :
    ExpDecayCInftyTube (fun q : ℝ × ℝ × ℂ =>
      cylJ Jbar q.1 q.2.1 q.2.2 - Jinf (q.2.1, q.2.2)) ρ b := by
  sorry

end FiniteEnergyPlane
