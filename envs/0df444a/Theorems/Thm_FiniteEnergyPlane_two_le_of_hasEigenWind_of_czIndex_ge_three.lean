-- Prove2me | Theorems.Thm_FiniteEnergyPlane_two_le_of_hasEigenWind_of_czIndex_ge_three
-- name    : FiniteEnergyPlane.two_le_of_hasEigenWind_of_czIndex_ge_three
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-01T15:38:20.792569+00:00
-- url     : https://prove2.me/theorems/3223ef29-28a6-4383-9f2e-e6acef852b59
-- title:
--   Large Conley–Zehnder index forces large windings of nonnegative eigenvalues
-- statement:
--   Let $H_0:\mathbb{R}^4\to\mathbb{R}$ have a strictly star-shaped level (in the sense of `HryniewiczCriterion`), $H$ the same function on $V=\mathbb{R}^{2\cdot(1+1)}$, $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$, $P$ a periodic orbit of $X_{H_0}$ on $H_0^{-1}(1)$ and $Q$ a nondegenerate periodic Reeb orbit of $H$ with the same image and with period equal to the action $\int_0^{T_P}\lambda_0(\dot x)$ of $P$. If $\mu_{CZ}(P)\ge3$, then every eigenvalue $\mu\ge0$ of the asymptotic operator $A_Q$ has winding at least $2$.
--
--   **Formalization Note** The orbits correspond as in `isNondegenerate_bridge` of the previous mission (transport by `Fin.cast`); the Conley–Zehnder index is `HryniewiczCriterion.czIndexOfPath (linearizedXiPath H₀ P Y)`, for every `Y` with `IsLinearizedFlow H₀ P.x Y`. The hypothesis is $3\le\mu_{CZ}$ for every such `Y`; windings of eigenvalues are `HasEigenWind J Q μ k`.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Lemma 4.5

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Hryniewicz (Trans. AMS 2012), Lemma 4.5: if a nondegenerate periodic Reeb orbit `Q` on
`S ⊂ ℝ⁴` has Conley–Zehnder index at least `3`, then every eigenvalue `μ ≥ 0` of its asymptotic
operator has eigenvectors of winding number at least `2` in the global frame. -/
theorem two_le_of_hasEigenWind_of_czIndex_ge_three (H₀ : HryniewiczCriterion.R4 → ℝ)
    (hH₀ : HryniewiczCriterion.IsStrictlyStarShapedLevel H₀) :
    let toV : HryniewiczCriterion.R4 → V 1 := fun x k => x (Fin.cast (by norm_num) k)
    let H : V 1 → ℝ := fun y => H₀ (fun k => y (Fin.cast (by norm_num) k))
    ∀ J : V 1 → V 1 →L[ℝ] V 1, IsCompatibleXiStructure H J →
    ∀ (P : HryniewiczCriterion.PeriodicOrbit H₀) (Q : ReebOrbit H),
      Set.range Q.x = Set.range (fun τ => toV (P.x τ)) →
      Q.T = ∫ τ in (0 : ℝ)..P.T, liouville (toV (P.x τ)) (deriv (fun s => toV (P.x s)) τ) →
      Q.IsNondegenerate →
      (∀ Y : ℝ → (HryniewiczCriterion.R4 →L[ℝ] HryniewiczCriterion.R4),
        HryniewiczCriterion.IsLinearizedFlow H₀ P.x Y →
        3 ≤ HryniewiczCriterion.czIndexOfPath (HryniewiczCriterion.linearizedXiPath H₀ P Y)) →
      ∀ μ : ℝ, 0 ≤ μ → ∀ k : ℤ, HasEigenWind J Q μ k → 2 ≤ k := by
  sorry

end FiniteEnergyPlane
