-- Prove2me | Theorems.Thm_FiniteEnergyPlane_isNondegenerate_bridge
-- name    : FiniteEnergyPlane.isNondegenerate_bridge
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-21T12:44:19.461117+00:00
-- url     : https://prove2.me/theorems/5c5f133c-b262-45e5-8b91-2f56ef71b177
-- title:
--   Nondegeneracy of Reeb orbits in $\mathbb{R}^4$ and of Hamiltonian periodic orbits
-- statement:
--   Let $H_0:\mathbb{R}^4\to\mathbb{R}$ have a strictly star-shaped level, in the sense of `HryniewiczCriterion`, and let $H$ be the same function on $V=\mathbb{R}^{2\cdot(1+1)}$. Let $P$ be a periodic orbit of $X_{H_0}$ on $H_0^{-1}(1)$ (in `HryniewiczCriterion`) and $Q$ a periodic Reeb orbit of $H$ with the same image and with period equal to the action $\int_0^{T_P}\lambda_0(\dot x)$ of $P$. Then $Q$ is nondegenerate if and only if, for the linearized flow $Y$ of $X_{H_0}$ along $P$, the path $\varphi$ of `HryniewiczCriterion.linearizedXiPath` satisfies: $\varphi(1)v=v$ only for $v=0$.
--
--   **Formalization Note** The coordinates are transported by `Fin.cast` along `2 * (1 + 1) = 4`, as in `periodicOrbit_bridge` of the previous mission. The right-hand side is the nondegeneracy hypothesis appearing in `HryniewiczCriterion` (for every `Y` with `IsLinearizedFlow H₀ P.x Y`).
-- source:
--   U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Section 2.1

import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Definitions.Def_HryniewiczCriterion_ConleyZehnder

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- For `n = 1`, nondegeneracy of a periodic Reeb orbit agrees with nondegeneracy of the
corresponding periodic orbit of `X_H` in `HryniewiczCriterion` (no eigenvalue `1` of the
linearized flow on `ξ` in the global frame). The coordinates are transported along
`Fin (2 * (1 + 1)) = Fin 4`; the orbits correspond by image and action, as in
`periodicOrbit_bridge`. -/
theorem isNondegenerate_bridge (H₀ : HryniewiczCriterion.R4 → ℝ)
    (hH₀ : HryniewiczCriterion.IsStrictlyStarShapedLevel H₀) :
    let toV : HryniewiczCriterion.R4 → V 1 := fun x k => x (Fin.cast (by norm_num) k)
    let H : V 1 → ℝ := fun y => H₀ (fun k => y (Fin.cast (by norm_num) k))
    ∀ (P : HryniewiczCriterion.PeriodicOrbit H₀) (Q : ReebOrbit H),
      Set.range Q.x = Set.range (fun τ => toV (P.x τ)) →
      Q.T = ∫ τ in (0 : ℝ)..P.T, liouville (toV (P.x τ)) (deriv (fun s => toV (P.x s)) τ) →
      (Q.IsNondegenerate ↔
        ∀ Y : ℝ → (HryniewiczCriterion.R4 →L[ℝ] HryniewiczCriterion.R4),
          HryniewiczCriterion.IsLinearizedFlow H₀ P.x Y →
          ∀ v : Fin 2 → ℝ, (HryniewiczCriterion.linearizedXiPath H₀ P Y 1).mulVec v = v →
            v = 0) := by
  sorry

end FiniteEnergyPlane
