-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_angle_gain_of_isCZAtLeast_three
-- name    : FiniteEnergyPlane.exists_angle_gain_of_isCZAtLeast_three
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-21T13:02:37.111927+00:00
-- url     : https://prove2.me/theorems/25370c3f-c9ed-4362-8c18-52843db25ec5
-- title:
--   Linearized solutions out-turn a winding-one loop along an orbit of CZ index at least three
-- statement:
--   Let $S = H^{-1}(1) \subset \mathbb{R}^4$ be strictly star-shaped, with a $d\lambda_0$-compatible complex structure $J$ on $\xi$. Let $P = (x, T)$ be a periodic Reeb orbit with $\mu_{CZ}(P) \geq 3$. Let $Z$ be a unitary frame of $\xi$ along $P$ whose windings agree with those of the global frame of $\xi$, and let $S_\infty$ be the symmetric loop that represents the asymptotic operator $A_P$ in this frame, $A_P(Z\eta) = Z(-J_0 \eta' - S_\infty \eta)$. Let $E : \mathbb{R} \to \mathbb{C}$ be a loop of winding number $1$.
--
--   Then there are $r > 0$ and $C \in \mathbb{R}$ with the following property. Let $\zeta : \mathbb{R} \to \mathbb{R}^2$ be a solution of $\zeta' = J_0 S_\infty(t)\, \zeta$ that is not identically zero. Then $\zeta$ (read as a complex number) has a continuous argument $\theta$. For every continuous argument $\beta$ of $E$ and all $t_0 \le t_1$,
--   $$(\theta(t_1) - \beta(t_1)) - (\theta(t_0) - \beta(t_0)) \;\ge\; r\,(t_1 - t_0) - C.$$
--
--   Role: a quantitative form of the statement that, for $\mu_{CZ}(P) \ge 3$, every nonzero solution of the linearized Reeb flow along $P$ turns by more than one full turn per period, uniformly. It is measured against any loop of winding one, such as a winding-one asymptotic eigenvector of a fast plane asymptotic to $P$.
--
--   Formalization Note: vectors of $\mathbb{R}^2$ = `CauchyRiemannIndex.Vec 1` are read as complex numbers through `vecToC`. The frame hypothesis `hwind` is the one supplied by `FiniteEnergyPlane.exists_unitaryXiFrame_hasXiLoopWind_iff`, and `hA` is the one supplied by `FiniteEnergyPlane.asympOp_frame_bridge`. The argument $\theta$ is produced by the conclusion, and the inequality holds for every continuous argument $\beta$ of $E$.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), Section 6.2 (proof of Lemma 6.9); H. Hofer, K. Wysocki, E. Zehnder, The dynamics on three-dimensional strictly convex energy surfaces, Ann. of Math. 148 (1998), Section 5

import Definitions.Def_FiniteEnergyPlane_OpenBook

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Solutions of the linearized equation along an orbit of Conley–Zehnder index at least `3`
gain angle on any winding-one loop at a uniform positive rate. -/
theorem exists_angle_gain_of_isCZAtLeast_three (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3)
    (Z : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1) (hZ : IsUnitaryXiFrame J P Z)
    (hwind : ∀ ζ : ℝ → CauchyRiemannIndex.Vec 1, Continuous ζ → Function.Periodic ζ 1 →
        (∀ t : ℝ, ζ t ≠ 0) → ∀ k : ℤ,
          (HasXiLoopWind P (fun t => Z t (ζ t)) k ↔ HasLoopWind (fun t => vecToC (ζ t)) k))
    (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (hSym : CauchyRiemannIndex.IsSymLoop Sinf)
    (hA : ∀ η : ℝ → CauchyRiemannIndex.Vec 1, ContDiff ℝ ∞ η → Function.Periodic η 1 →
        ∀ t : ℝ, asympOp J P (fun t => Z t (η t)) t =
          Z t (-(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) (deriv η t)) -
            Matrix.toEuclideanLin (Sinf t) (η t)))
    (E : ℝ → ℂ) (hE : HasLoopWind E 1) :
    ∃ r > 0, ∃ C : ℝ, ∀ ζ : ℝ → CauchyRiemannIndex.Vec 1,
      (∀ t : ℝ, HasDerivAt ζ
        (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1 * Sinf t) (ζ t)) t) →
      (∃ t : ℝ, ζ t ≠ 0) →
      ∃ θ : ℝ → ℝ, Continuous θ ∧
        (∀ t : ℝ, vecToC (ζ t) =
          (‖vecToC (ζ t)‖ : ℂ) * Complex.exp ((θ t : ℂ) * Complex.I)) ∧
        ∀ β : ℝ → ℝ, Continuous β →
          (∀ t : ℝ, E t = (‖E t‖ : ℂ) * Complex.exp ((β t : ℂ) * Complex.I)) →
          ∀ t₀ t₁ : ℝ, t₀ ≤ t₁ → r * (t₁ - t₀) - C ≤ (θ t₁ - β t₁) - (θ t₀ - β t₀) := by
  sorry

end FiniteEnergyPlane
