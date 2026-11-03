-- Prove2me | Theorems.Thm_FiniteEnergyPlane_czIndexOfPath_eq_alphaMinus_add_alphaPlus
-- name    : FiniteEnergyPlane.czIndexOfPath_eq_alphaMinus_add_alphaPlus
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-01T15:38:06.997271+00:00
-- url     : https://prove2.me/theorems/000a8fce-802e-46ee-9573-0471aa7e9681
-- title:
--   The Conley–Zehnder index of a nondegenerate orbit in terms of eigenvector windings
-- statement:
--   Let $H_0:\mathbb{R}^4\to\mathbb{R}$ have a strictly star-shaped level (in the sense of `HryniewiczCriterion`), $H$ the same function on $V=\mathbb{R}^{2\cdot(1+1)}$, $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$, $P$ a periodic orbit of $X_{H_0}$ on $H_0^{-1}(1)$ and $Q$ a nondegenerate periodic Reeb orbit of $H$ with the same image and with period equal to the action $\int_0^{T_P}\lambda_0(\dot x)$ of $P$. Then $\alpha^-(Q)$ and $\alpha^+(Q)$ exist, the parity $p=\alpha^+(Q)-\alpha^-(Q)$ is $0$ or $1$, and
--   $$\mu_{CZ}(P)=2\alpha^-(Q)+p=\alpha^-(Q)+\alpha^+(Q).$$
--
--   **Formalization Note** The orbits correspond as in `isNondegenerate_bridge` of the previous mission (transport by `Fin.cast`); the Conley–Zehnder index is `HryniewiczCriterion.czIndexOfPath (linearizedXiPath H₀ P Y)`, for every `Y` with `IsLinearizedFlow H₀ P.x Y`. $\alpha^\pm$ are `IsAlphaMinus J Q a`, `IsAlphaPlus J Q b`, windings in the global frame.
-- source:
--   H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations II: Embedding controls and algebraic invariants, Geom. Funct. Anal. 5 (1995), 270–328, Theorem 3.10; C. Wendl, Lectures on Symplectic Field Theory, lecture notes, Humboldt-Universität zu Berlin (2026 version); earlier version arXiv:1612.01009, Theorem 3.7.2

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Hofer–Wysocki–Zehnder (GAFA 1995, Theorem 3.10); Wendl, Theorem 3.7.2: for a nondegenerate
periodic Reeb orbit `Q` on `S ⊂ ℝ⁴`, the numbers `α⁻(Q)` and `α⁺(Q)` (windings of the asymptotic
operator's eigenvectors in the global frame) exist, the parity `p = α⁺ - α⁻` is `0` or `1`, and
the Conley–Zehnder index of the corresponding periodic orbit `P` in `HryniewiczCriterion` is
`μ_CZ = 2α⁻ + p = α⁻ + α⁺`. The orbits `P` and `Q` correspond by image and action, as in
`isNondegenerate_bridge`. -/
theorem czIndexOfPath_eq_alphaMinus_add_alphaPlus (H₀ : HryniewiczCriterion.R4 → ℝ)
    (hH₀ : HryniewiczCriterion.IsStrictlyStarShapedLevel H₀) :
    let toV : HryniewiczCriterion.R4 → V 1 := fun x k => x (Fin.cast (by norm_num) k)
    let H : V 1 → ℝ := fun y => H₀ (fun k => y (Fin.cast (by norm_num) k))
    ∀ J : V 1 → V 1 →L[ℝ] V 1, IsCompatibleXiStructure H J →
    ∀ (P : HryniewiczCriterion.PeriodicOrbit H₀) (Q : ReebOrbit H),
      Set.range Q.x = Set.range (fun τ => toV (P.x τ)) →
      Q.T = ∫ τ in (0 : ℝ)..P.T, liouville (toV (P.x τ)) (deriv (fun s => toV (P.x s)) τ) →
      Q.IsNondegenerate →
      ∃ a b : ℤ, IsAlphaMinus J Q a ∧ IsAlphaPlus J Q b ∧ (b = a ∨ b = a + 1) ∧
        ∀ Y : ℝ → (HryniewiczCriterion.R4 →L[ℝ] HryniewiczCriterion.R4),
          HryniewiczCriterion.IsLinearizedFlow H₀ P.x Y →
          HryniewiczCriterion.czIndexOfPath (HryniewiczCriterion.linearizedXiPath H₀ P Y) =
            a + b := by
  sorry

end FiniteEnergyPlane
