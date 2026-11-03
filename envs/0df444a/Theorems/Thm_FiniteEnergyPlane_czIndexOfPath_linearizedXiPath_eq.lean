-- Prove2me | Theorems.Thm_FiniteEnergyPlane_czIndexOfPath_linearizedXiPath_eq
-- name    : FiniteEnergyPlane.czIndexOfPath_linearizedXiPath_eq
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-02T16:24:31.051168+00:00
-- url     : https://prove2.me/theorems/dcaa1731-f6c4-4b1a-a2c3-9cdb015bad88
-- title:
--   The Conley–Zehnder index of a periodic orbit equals the index of its asymptotic operator's matrix form
-- statement:
--   Let $H_0:\mathbb{R}^4\to\mathbb{R}$ have a strictly star-shaped level $S=H_0^{-1}(1)$ and let $H$ be the same function on $V=\mathbb{R}^{2\cdot(1+1)}$. Let $P=(x,T_P)$ be a periodic orbit of $X_{H_0}$ on $S$, and $Q$ a nondegenerate periodic Reeb orbit with the same image, with period equal to the action $\int_0^{T_P}\lambda_0(\dot x)$, and with the same starting point, $Q(0)=x(0)$. Let $Z$ be a unitary frame of $\xi$ along $Q$ homotopic to the global frame (a loop $t\mapsto Z(t)\zeta(t)$ has the same winding number in the global frame as $\zeta$ has in $\mathbb{C}$), and let $S_\infty$ be a smooth $1$-periodic loop of symmetric $2\times2$ matrices representing the asymptotic operator of $Q$ in this frame, $A_Q(Z\eta)=Z(-J_0\eta'-S_\infty\eta)$ for smooth $1$-periodic $\eta$. Let $\Psi$ be the fundamental solution of $S_\infty$ ($\Psi(0)=I$, $\Psi'=J_0S_\infty\Psi$).
--
--   Then the Conley–Zehnder index of $P$ (Hryniewicz's index of the linearized flow on $\xi$ in the global frame) equals Hryniewicz's index of the path $t\mapsto\Psi(t)$, $t\in[0,1]$.
--
--   This identifies the Conley–Zehnder index of a periodic orbit in Hryniewicz's convention with the index of the matrix form of its asymptotic operator.
--
--   **Formalization Note** The orbits correspond as in `isNondegenerate_bridge` (transport by `Fin.cast`), with the extra condition `Q.x 0 = toV (P.x 0)`. The left side is `HryniewiczCriterion.czIndexOfPath (linearizedXiPath H₀ P Y)` for every `Y` with `IsLinearizedFlow H₀ P.x Y`; on the right, matrices are transported along `finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2`. The frame hypotheses are those provided by `exists_unitaryXiFrame_hasXiLoopWind_iff` and `asympOp_frame_bridge`.
-- source:
--   H. Hofer, K. Wysocki, E. Zehnder, GAFA 5 (1995), Theorem 3.10; U. Hryniewicz, J. Symplectic Geom. 12 (2014), Remark 2.6 (auxiliary lemma)

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- The Conley–Zehnder index of a nondegenerate periodic orbit `P` of `X_{H₀}` in
`HryniewiczCriterion` (linearized flow on `ξ` in the global frame) equals Hryniewicz's index of
the fundamental solution `Ψ` of any loop `S∞` that represents the asymptotic operator of the
corresponding Reeb orbit `Q` in a unitary frame `Z` homotopic to the global frame. The orbits
correspond by image and action as in `isNondegenerate_bridge`, and start at the same point. -/
theorem czIndexOfPath_linearizedXiPath_eq (H₀ : HryniewiczCriterion.R4 → ℝ)
    (hH₀ : HryniewiczCriterion.IsStrictlyStarShapedLevel H₀) :
    let toV : HryniewiczCriterion.R4 → V 1 := fun x k => x (Fin.cast (by norm_num) k)
    let H : V 1 → ℝ := fun y => H₀ (fun k => y (Fin.cast (by norm_num) k))
    ∀ J : V 1 → V 1 →L[ℝ] V 1,
    ∀ (P : HryniewiczCriterion.PeriodicOrbit H₀) (Q : ReebOrbit H),
      Set.range Q.x = Set.range (fun τ => toV (P.x τ)) →
      Q.T = ∫ τ in (0 : ℝ)..P.T, liouville (toV (P.x τ)) (deriv (fun s => toV (P.x s)) τ) →
      Q.x 0 = toV (P.x 0) →
      Q.IsNondegenerate →
      ∀ Z : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1, IsUnitaryXiFrame J Q Z →
      (∀ ζ : ℝ → CauchyRiemannIndex.Vec 1, Continuous ζ → Function.Periodic ζ 1 →
        (∀ t : ℝ, ζ t ≠ 0) → ∀ k : ℤ,
          (HasXiLoopWind Q (fun t => Z t (ζ t)) k ↔ HasLoopWind (fun t => vecToC (ζ t)) k)) →
      ∀ Sinf : ℝ → CauchyRiemannIndex.Mat 1, CauchyRiemannIndex.IsSymLoop Sinf →
      (∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j)) →
      (∀ η : ℝ → CauchyRiemannIndex.Vec 1, ContDiff ℝ ∞ η → Function.Periodic η 1 →
        ∀ t : ℝ, asympOp J Q (fun t => Z t (η t)) t =
          Z t (-(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) (deriv η t)) -
            Matrix.toEuclideanLin (Sinf t) (η t))) →
      ∀ Ψ : ℝ → CauchyRiemannIndex.Mat 1, CauchyRiemannIndex.IsFundamentalSolution Sinf Ψ →
      ∀ Y : ℝ → (HryniewiczCriterion.R4 →L[ℝ] HryniewiczCriterion.R4),
        HryniewiczCriterion.IsLinearizedFlow H₀ P.x Y →
        HryniewiczCriterion.czIndexOfPath (HryniewiczCriterion.linearizedXiPath H₀ P Y) =
          HryniewiczCriterion.czIndexOfPath
            (fun τ => Matrix.reindex finSumFinEquiv finSumFinEquiv (Ψ τ)) := by
  sorry

end FiniteEnergyPlane
