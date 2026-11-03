-- Prove2me | Theorems.Thm_FiniteEnergyPlane_hasEigenWind_iff_hasLoopEigenWind
-- name    : FiniteEnergyPlane.hasEigenWind_iff_hasLoopEigenWind
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-02T16:24:32.166003+00:00
-- url     : https://prove2.me/theorems/0404fc2f-d1d6-46b1-ad15-71467a983a53
-- title:
--   Eigenvector windings of the asymptotic operator agree with those of its matrix form in a unitary frame
-- statement:
--   Let $P=(x,T)$ be a periodic Reeb orbit on a star-shaped level $S\subset\mathbb{R}^4$ and $J$ a complex structure on $\xi$. Let $Z(t):\mathbb{R}^2\to\xi_{x(Tt)}$ be a unitary frame of $\xi$ along $P$ which is homotopic to the global frame, in the sense that for every continuous $1$-periodic nowhere-vanishing $\zeta:\mathbb{R}\to\mathbb{R}^2$ the loop $t\mapsto Z(t)\zeta(t)$ has winding number $k$ in the global frame if and only if $\zeta$ has winding number $k$ in $\mathbb{C}$. Let $S_\infty$ be a smooth $1$-periodic loop of symmetric $2\times2$ matrices representing the asymptotic operator in this frame: $A_P(Z\eta)=Z(-J_0\eta'-S_\infty\eta)$ for smooth $1$-periodic $\eta$.
--
--   Then for all $\mu\in\mathbb{R}$, $k\in\mathbb{Z}$: $\mu$ is an eigenvalue of $A_P$ all of whose eigenvectors have winding $k$ in the global frame if and only if $\mu$ is an eigenvalue of $-J_0\partial_t-S_\infty$ all of whose eigenfunctions have winding $k$.
--
--   This transfers the windings of eigenvectors between the asymptotic operator of a Reeb orbit and its matrix form in a unitary frame.
--
--   **Formalization Note** The frame is `IsUnitaryXiFrame J P Z`; the two winding properties are `HasEigenWind J P μ k` and `HasLoopEigenWind Sinf μ k`. The frame hypotheses are those provided by `exists_unitaryXiFrame_hasXiLoopWind_iff` and `asympOp_frame_bridge`.
-- source:
--   H. Hofer, K. Wysocki, E. Zehnder, GAFA 5 (1995), Theorem 3.10; U. Hryniewicz, J. Symplectic Geom. 12 (2014), Remark 2.6 (auxiliary lemma)

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Let `Z` be a unitary frame of `ξ` along `P` that is homotopic to the global frame (a loop
`t ↦ Z(t) ζ(t)` has the same winding in the global frame as `ζ` has in `ℂ`), and let `S∞` be a
smooth loop of symmetric matrices that represents `A_P` in this frame,
`A_P (Z η) = Z (-J₀ η' - S∞ η)`. Then `μ` is an eigenvalue of `A_P` whose eigenvectors have
winding `k` in the global frame if and only if `μ` is an eigenvalue of `-J₀ ∂ₜ - S∞` whose
eigenfunctions have winding `k`. -/
theorem hasEigenWind_iff_hasLoopEigenWind {H : V 1 → ℝ} (J : V 1 → V 1 →L[ℝ] V 1)
    (P : ReebOrbit H) (Z : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1)
    (hZ : IsUnitaryXiFrame J P Z)
    (hwind : ∀ ζ : ℝ → CauchyRiemannIndex.Vec 1, Continuous ζ → Function.Periodic ζ 1 →
      (∀ t : ℝ, ζ t ≠ 0) → ∀ k : ℤ,
        (HasXiLoopWind P (fun t => Z t (ζ t)) k ↔ HasLoopWind (fun t => vecToC (ζ t)) k))
    (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (hA : ∀ η : ℝ → CauchyRiemannIndex.Vec 1, ContDiff ℝ ∞ η → Function.Periodic η 1 →
      ∀ t : ℝ, asympOp J P (fun t => Z t (η t)) t =
        Z t (-(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) (deriv η t)) -
          Matrix.toEuclideanLin (Sinf t) (η t)))
    (μ : ℝ) (k : ℤ) :
    HasEigenWind J P μ k ↔ HasLoopEigenWind Sinf μ k := by
  sorry

end FiniteEnergyPlane
