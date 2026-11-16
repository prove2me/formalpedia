-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_tubeModel_of_unitaryXiFrame
-- name    : FiniteEnergyPlane.exists_tubeModel_of_unitaryXiFrame
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-15T17:20:24.129674+00:00
-- url     : https://prove2.me/theorems/4a2e5084-f619-403b-b115-f072d12cd251
-- title:
--   The limit model of a standard tube along a Reeb orbit
-- statement:
--   Let $S=H^{-1}(1)$ be strictly star-shaped, $J$ a compatible complex structure on $\xi$, $\tilde J$ the induced almost complex structure on $\mathbb R^4\setminus\{0\}$, and $P=(x,T)$ a periodic Reeb orbit. Let $M(t)$ be a unitary frame of $\xi$ along $P$ and $S_\infty$ a loop of real $2\times2$ matrices with $A_P(M\eta)=M(-J_0\eta'-S_\infty\eta)$ for every smooth $1$-periodic $\eta$. Put $m(t,w)=x(Tt)+M(t)w$ (with $w\in\mathbb C=\mathbb R^2$) and let $L(t,w)$ be the derivative of $(\zeta,w)\mapsto e^{2T\,\mathrm{Re}\,\zeta}\,m(\mathrm{Im}\,\zeta,w)$ at $(it,w)$.
--
--   Then there are $\rho>0$ and a $1$-periodic family $J_\infty(t,w)$ of real linear maps of $\mathbb C^2$, smooth on $\mathbb R\times B_\rho$, such that: for $|w|\le\rho$, $m(t,w)\neq0$ and $L(t,w)$ is injective; for $|w|<\rho$, $L(t,w)\circ J_\infty(t,w)=\tilde J(m(t,w))\circ L(t,w)$; and $S_\infty(t)a$ is the second component of $(\partial_wJ_\infty(t,0)a)(i,0)$ for every $a\in\mathbb R^2$.
--
--   This is the $t$-periodic limit structure at the end of a standard tube around a plane asymptotic to $P$ (the map $L$ is the asymptotic shape of the tube parametrisation in cylinder coordinates), together with the identification of its normal linearisation with the asymptotic operator of $P$.
--
--   Formalization Note: $\mathbb R^2$ and $\mathbb C$ are identified by `cToVec`/`vecToC`; the derivative $L(t,w)$ is written as `fderiv` of the explicit map at `((t : ℂ) * I, w)`; $\tilde J$ is `Jtilde H J`, the frame hypothesis is `IsUnitaryXiFrame J P M` and $A_P$ is `asympOp J P`.
-- source:
--   Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), Section 6

import Definitions.Def_FiniteEnergyPlane_TubeFamily
import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- The limit model of a standard tube along a Reeb orbit. Let `M` be a unitary frame of `ξ`
along `P` and `Sinf` a loop of real `2 × 2` matrices with `A_P (M η) = M (-J₀ η' - Sinf η)` for
smooth `1`-periodic `η`. Put `m(t, w) = x(T t) + M(t)(cToVec w)` and let `L(t, w)` be the
derivative of `(ζ, w) ↦ e^{2T Re ζ} m(Im ζ, w)` at `(i t, w)`. Then there are `ρ > 0` and a
`1`-periodic family `Jinf(t, w)` of real linear maps of `ℂ × ℂ`, smooth on `ℝ × ball 0 ρ`, such
that for `|w| ≤ ρ` the point `m(t, w)` is nonzero and `L(t, w)` is injective, for `|w| < ρ`
`L(t, w) ∘ Jinf(t, w) = J̃(m(t, w)) ∘ L(t, w)`, and `Sinf(t) a` is the second component of
`(∂_w Jinf(t, 0) a)(i, 0)`. -/
theorem exists_tubeModel_of_unitaryXiFrame (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J) (P : ReebOrbit H)
    (M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1) (hM : IsUnitaryXiFrame J P M)
    (Sinf : ℝ → CauchyRiemannIndex.Mat 1)
    (hA : ∀ η : ℝ → CauchyRiemannIndex.Vec 1, ContDiff ℝ ∞ η → Function.Periodic η 1 →
      ∀ t : ℝ, asympOp J P (fun t => M t (η t)) t =
        M t (-(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) (deriv η t)) -
          Matrix.toEuclideanLin (Sinf t) (η t))) :
    ∃ ρ > 0, ∃ Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ,
      (∀ (t : ℝ) (w : ℂ), w ∈ closedBall (0 : ℂ) ρ →
        P.x (P.T * t) + M t (cToVec w) ≠ 0 ∧
        Function.Injective (fderiv ℝ (fun q : ℂ × ℂ => Real.exp (2 * P.T * q.1.re) •
          (P.x (P.T * q.1.im) + M q.1.im (cToVec q.2))) ((t : ℂ) * Complex.I, w))) ∧
      ContDiffOn ℝ ∞ Jinf (Set.univ ×ˢ ball (0 : ℂ) ρ) ∧
      (∀ (t : ℝ) (w : ℂ), Jinf (t + 1, w) = Jinf (t, w)) ∧
      (∀ (t : ℝ) (w : ℂ), w ∈ ball (0 : ℂ) ρ →
        (fderiv ℝ (fun q : ℂ × ℂ => Real.exp (2 * P.T * q.1.re) •
          (P.x (P.T * q.1.im) + M q.1.im (cToVec q.2))) ((t : ℂ) * Complex.I, w)).comp
            (Jinf (t, w)) =
          (Jtilde H J (P.x (P.T * t) + M t (cToVec w))).comp
            (fderiv ℝ (fun q : ℂ × ℂ => Real.exp (2 * P.T * q.1.re) •
              (P.x (P.T * q.1.im) + M q.1.im (cToVec q.2))) ((t : ℂ) * Complex.I, w))) ∧
      ∀ (t : ℝ) (a : CauchyRiemannIndex.Vec 1),
        vecToC (Matrix.toEuclideanLin (Sinf t) a) =
          ((fderiv ℝ (fun w : ℂ => Jinf (t, w)) 0 (vecToC a)) (Complex.I, 0)).2 := by
  sorry

end FiniteEnergyPlane
