-- Prove2me | Theorems.Thm_FiniteEnergyPlane_hasEigenWind_succ_of_unitaryXiFrame
-- name    : FiniteEnergyPlane.hasEigenWind_succ_of_unitaryXiFrame
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-14T19:23:58.557317+00:00
-- url     : https://prove2.me/theorems/5eb0ebfd-eece-4b75-bdf6-92772027fb5f
-- title:
--   Eigenvalue windings through a unitary frame of winding one
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb R^4$, $J$ a complex structure on $\xi$, and $P=(x,T)$ a periodic Reeb orbit with asymptotic operator $A_P$. Let $M(t):\mathbb R^2\to\xi_{x(Tt)}$ be a unitary frame of $\xi$ along $P$ of winding one: a continuous $1$-periodic nowhere-vanishing loop $\zeta$ in $\mathbb R^2\cong\mathbb C$ has winding number $k$ if and only if the loop $t\mapsto M(t)\zeta(t)$ has winding number $k+1$ in the global frame of $\xi$. Let $S_\infty$ be a smooth symmetric $1$-periodic loop of real $2\times2$ matrices with $A_P(M\eta)=M(-J_0\eta'-S_\infty\eta)$ for every smooth $1$-periodic $\eta$.
--
--   If $\mu$ is an eigenvalue of $-J_0\partial_t-S_\infty$ and every eigenfunction for $\mu$ has winding number $k$, then $\mu$ is an eigenvalue of $A_P$ and every eigenvector of $A_P$ for $\mu$ has winding number $k+1$ in the global frame.
--
--   This converts winding statements about the loop operator of a frame into the global-frame windings of Hryniewicz's asymptotic operator when the frame itself winds once.
--
--   Formalization Note: the hypotheses are `IsUnitaryXiFrame J P M`, the winding equivalence via `HasXiLoopWind` / `HasLoopWind`, `IsSymLoop Sinf`, smooth entries, and the operator identity with `asympOp`; the conclusion is `HasLoopEigenWind Sinf μ k → HasEigenWind J P μ (k + 1)`.
-- source:
--   Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), proof of Lemma 6.10

import Definitions.Def_FiniteEnergyPlane_TubeFamily
import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Eigen-windings through a unitary frame of winding one. Let `M` be a unitary frame of `ξ`
along the periodic Reeb orbit `P` such that a nowhere-vanishing loop `ζ` has winding `k` iff `M ζ`
has winding `k + 1` in the global frame, and let `Sinf` be a smooth symmetric loop with
`A_P (M η) = M (-J₀ η' - Sinf η)` for smooth `1`-periodic `η`. If every eigenfunction of
`-J₀ ∂ₜ - Sinf` for the eigenvalue `μ` has winding `k`, then `μ` is an eigenvalue of `A_P` and every
eigenvector for `μ` has winding `k + 1`. -/
theorem hasEigenWind_succ_of_unitaryXiFrame {H : V 1 → ℝ} (J : V 1 → V 1 →L[ℝ] V 1)
    (P : ReebOrbit H) (M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1) (hM : IsUnitaryXiFrame J P M)
    (hwind : ∀ ζ : ℝ → CauchyRiemannIndex.Vec 1, Continuous ζ → Function.Periodic ζ 1 →
      (∀ t : ℝ, ζ t ≠ 0) → ∀ k : ℤ,
        (HasXiLoopWind P (fun t => M t (ζ t)) (k + 1) ↔ HasLoopWind (fun t => vecToC (ζ t)) k))
    (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (hA : ∀ η : ℝ → CauchyRiemannIndex.Vec 1, ContDiff ℝ ∞ η → Function.Periodic η 1 →
      ∀ t : ℝ, asympOp J P (fun t => M t (η t)) t =
        M t (-(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) (deriv η t)) -
          Matrix.toEuclideanLin (Sinf t) (η t)))
    (μ : ℝ) (k : ℤ) (h : HasLoopEigenWind Sinf μ k) :
    HasEigenWind J P μ (k + 1) := by
  sorry

end FiniteEnergyPlane
