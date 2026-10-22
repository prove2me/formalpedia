-- Prove2me | Theorems.Thm_FiniteEnergyPlane_asympOp_frame_bridge
-- name    : FiniteEnergyPlane.asympOp_frame_bridge
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-21T12:42:00.94403+00:00
-- url     : https://prove2.me/theorems/e8b03002-052d-425e-82be-87cf9679e4dc
-- title:
--   The asymptotic operator in a unitary frame
-- statement:
--   Let $S=H^{-1}(1)$ be a strictly star-shaped level, $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$, and $P=(x,T)$ a periodic Reeb orbit. A unitary frame $Z$ of $\xi$ along $P$ exists. For every unitary frame $Z$ there is a $C^\infty$ $1$-periodic loop $S_\infty$ of symmetric $2n\times2n$ matrices such that
--   $$A_P\big(Z\eta\big)(t)=Z(t)\big(-J_0\eta'(t)-S_\infty(t)\eta(t)\big)$$
--   for every $C^\infty$ $1$-periodic $\eta:\mathbb{R}\to\mathbb{R}^{2n}$ and every $t$, and $P$ is nondegenerate if and only if the asymptotic operator $-J_0\partial_t-S_\infty$ is nondegenerate.
--
--   **Formalization Note** $Z\eta$ is `fun t => Z t (η t)`. Symmetric loops and nondegeneracy are `CauchyRiemannIndex.IsSymLoop` and `CauchyRiemannIndex.IsNondegenerate` (no fundamental solution of $\Psi'=J_0S_\infty\Psi$, $\Psi(0)=1$, has $\det(1-\Psi(1))=0$).
-- source:
--   U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Remark 2.6

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Hryniewicz, Remark 2.6: a unitary frame of `ξ` along `P` exists, and in any such frame `Z`
the asymptotic operator takes the form `-J₀ ∂ₜ - S∞(t)` for a smooth loop `S∞` of symmetric
matrices: `A_P (Z η) = Z (-J₀ η' - S∞ η)`. Moreover `P` is nondegenerate if and only if
`-J₀ ∂ₜ - S∞` is nondegenerate in the sense of `CauchyRiemannIndex.IsNondegenerate`. -/
theorem asympOp_frame_bridge {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (P : ReebOrbit H) :
    (∃ Z : ℝ → CauchyRiemannIndex.Vec n →L[ℝ] V n, IsUnitaryXiFrame J P Z) ∧
      ∀ Z : ℝ → CauchyRiemannIndex.Vec n →L[ℝ] V n, IsUnitaryXiFrame J P Z →
        ∃ Sinf : ℝ → CauchyRiemannIndex.Mat n, CauchyRiemannIndex.IsSymLoop Sinf ∧
          (∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j)) ∧
          (∀ η : ℝ → CauchyRiemannIndex.Vec n, ContDiff ℝ ∞ η → Function.Periodic η 1 →
            ∀ t : ℝ, asympOp J P (fun t => Z t (η t)) t =
              Z t (-(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ n) (deriv η t)) -
                Matrix.toEuclideanLin (Sinf t) (η t))) ∧
          (P.IsNondegenerate ↔ CauchyRiemannIndex.IsNondegenerate Sinf) := by
  sorry

end FiniteEnergyPlane
