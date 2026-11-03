-- Prove2me | Theorems.Thm_ConleyZehnder_czIndex_one_eq_of_rhoHat_lift
-- name    : ConleyZehnder.czIndex_one_eq_of_rhoHat_lift
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-02T16:02:05.366134+00:00
-- url     : https://prove2.me/theorems/2576b451-9331-4404-b476-5c3a80e02f5c
-- title:
--   The Conley–Zehnder index of a path in Sp(2) from the rotation of its normalized complex determinant
-- statement:
--   Let $\psi:[0,1]\to\mathrm{Sp}(2)$ be continuous with $\psi(0)=\mathrm{Id}$ and $\det(\mathrm{Id}-\psi(1))\neq0$, and let $\theta:[0,1]\to\mathbb{R}$ be continuous with $\hat\rho(\psi(t))=e^{i\theta(t)}$ for all $t$, where $\hat\rho$ is the normalized complex determinant of the complex-linear part. Let $k\in\mathbb{Z}$ and $\Delta=\theta(1)-\theta(0)$.
--
--   1. If $\operatorname{tr}\psi(1)>2$ and $|\Delta-2\pi k|<\pi/2$, then $\mu_{CZ}(\psi)=2k$.
--   2. If $\operatorname{tr}\psi(1)<2$ and $2\pi k<\Delta<2\pi k+2\pi$, then $\mu_{CZ}(\psi)=2k+1$.
--
--   This computes the Conley–Zehnder index of a path in $\mathrm{Sp}(2)$ from the total rotation of $\hat\rho$ along the path and the trace of its end point.
--
--   **Formalization Note** $\psi$ is an element of `ConleyZehnder.SP 1` ($\mathbb{R}^2$ indexed by `Fin 1 ⊕ Fin 1`), $\hat\rho$ is `ConleyZehnder.rhoHat`, $\mu_{CZ}$ is `ConleyZehnder.czIndex`, and $\theta$ is given by `ConleyZehnder.IsArgLift`.
-- source:
--   J. Gutt, Generalized Conley–Zehnder index, Ann. Fac. Sci. Toulouse Math. 23 (2014), arXiv:1307.7239, Section 2

import Definitions.Def_ConleyZehnder_Setting

namespace ConleyZehnder

/-- For a path `ψ ∈ SP(1)` and a continuous argument `θ` of `ρ̂ ∘ ψ`: if `tr ψ(1) > 2` and the
increment of `θ` lies within `π/2` of `2πk`, then `μ_CZ(ψ) = 2k`; if `tr ψ(1) < 2` and the
increment of `θ` lies in `(2πk, 2πk + 2π)`, then `μ_CZ(ψ) = 2k + 1`. -/
theorem czIndex_one_eq_of_rhoHat_lift (ψ : C(unitInterval, Mat 1)) (hψ : ψ ∈ SP 1)
    (θ : unitInterval → ℝ) (hθ : IsArgLift (fun t => rhoHat (ψ t)) θ) (k : ℤ) :
    (2 < (ψ 1).trace → |θ 1 - θ 0 - 2 * Real.pi * k| < Real.pi / 2 → czIndex ψ = 2 * k) ∧
    ((ψ 1).trace < 2 → 2 * Real.pi * k < θ 1 - θ 0 → θ 1 - θ 0 < 2 * Real.pi * k + 2 * Real.pi →
      czIndex ψ = 2 * k + 1) := by
  sorry

end ConleyZehnder
