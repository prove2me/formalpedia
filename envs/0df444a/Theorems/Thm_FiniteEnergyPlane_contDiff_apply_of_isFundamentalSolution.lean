-- Prove2me | Theorems.Thm_FiniteEnergyPlane_contDiff_apply_of_isFundamentalSolution
-- name    : FiniteEnergyPlane.contDiff_apply_of_isFundamentalSolution
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-06T14:22:30.504433+00:00
-- url     : https://prove2.me/theorems/eac267aa-23b5-49fb-933c-49161b37d121
-- title:
--   Entries of a fundamental solution of a smooth loop are smooth
-- statement:
--   Let $S_\infty$ be a loop of matrices with smooth entries and $\Psi$ its fundamental solution, $\Psi(0) = I$, $\Psi' = J_0 S_\infty \Psi$. Then every entry of $\Psi$ is smooth.
--
--   **Role.** This gives the regularity needed to apply statements about smooth symplectic paths to fundamental solutions.
-- source:
--   Standard regularity for linear ordinary differential equations

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open scoped ContDiff

/-- The entries of the fundamental solution of a loop with smooth entries are smooth. -/
theorem contDiff_apply_of_isFundamentalSolution (Sinf : ℝ → CauchyRiemannIndex.Mat 1)
    (hS : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (Ψ : ℝ → CauchyRiemannIndex.Mat 1) (hΨ : CauchyRiemannIndex.IsFundamentalSolution Sinf Ψ) :
    ∀ i j, ContDiff ℝ ∞ (fun t => Ψ t i j) := by
  sorry

end FiniteEnergyPlane
