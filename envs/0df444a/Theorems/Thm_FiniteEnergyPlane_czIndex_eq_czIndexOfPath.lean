-- Prove2me | Theorems.Thm_FiniteEnergyPlane_czIndex_eq_czIndexOfPath
-- name    : FiniteEnergyPlane.czIndex_eq_czIndexOfPath
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-01T15:37:50.216371+00:00
-- url     : https://prove2.me/theorems/81161b26-b76f-41d4-a247-7c3bcd82b434
-- title:
--   Two definitions of the Conley–Zehnder index in dimension two agree
-- statement:
--   Let $\psi:[0,1]\to\mathrm{Sp}(2)$ be continuous with $\psi(0)=\mathrm{Id}$ and $\det(\mathrm{Id}-\psi(1))\neq0$. Then the Conley–Zehnder index of $\psi$ in the sense of `ConleyZehnder` (the degree of $\hat\rho^2$ along $\psi$ extended in $\mathrm{Sp}^*$) equals Hryniewicz's index $\mu(\psi)$ defined from the winding interval of $\psi$.
--
--   **Formalization Note** $\psi$ is an element of `ConleyZehnder.SP 1`, with $\mathbb{R}^2$ indexed by `Fin 1 ⊕ Fin 1` as $(q,p)$. It is transported to `Matrix (Fin 2) (Fin 2) ℝ` by `finSumFinEquiv` ($q\mapsto0$, $p\mapsto1$) and extended to $\mathbb{R}$ by `Set.projIcc 0 1`, constant outside $[0,1]$.
-- source:
--   J. Gutt, Generalized Conley–Zehnder index, Ann. Fac. Sci. Toulouse Math. 23 (2014), arXiv:1307.7239, Section 2; U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Section 2.1.1

import Definitions.Def_FiniteEnergyPlane_Winding
import Definitions.Def_ConleyZehnder_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- For nondegenerate paths in `Sp(2)`, the Conley–Zehnder index `ConleyZehnder.czIndex` agrees with
Hryniewicz's index `HryniewiczCriterion.czIndexOfPath` of the winding interval. The matrices are
transported along `Fin 1 ⊕ Fin 1 ≃ Fin 2` (`q ↦ 0`, `p ↦ 1`), and the path is extended to `ℝ` as
constant outside `[0, 1]`. -/
theorem czIndex_eq_czIndexOfPath (ψ : C(unitInterval, ConleyZehnder.Mat 1))
    (hψ : ψ ∈ ConleyZehnder.SP 1) :
    ConleyZehnder.czIndex ψ = HryniewiczCriterion.czIndexOfPath (fun τ =>
      Matrix.reindex finSumFinEquiv finSumFinEquiv (ψ (Set.projIcc 0 1 zero_le_one τ))) := by
  sorry

end FiniteEnergyPlane
