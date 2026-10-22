-- Prove2me | Theorems.Thm_FiniteEnergyPlane_asympOp_eq_zero_iff
-- name    : FiniteEnergyPlane.asympOp_eq_zero_iff
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-21T12:41:43.808221+00:00
-- url     : https://prove2.me/theorems/bf9e41c6-b3b6-488e-ab88-d85dc813743b
-- title:
--   The kernel of the asymptotic operator
-- statement:
--   Let $S=H^{-1}(1)$ be a strictly star-shaped level, $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$, and $P=(x,T)$ a periodic Reeb orbit with linearized Reeb flow $\Phi$. A $\xi$-loop $\eta$ along $P$ satisfies $A_P\eta=0$ if and only if $\eta(t)=\Phi(Tt)\eta(0)$ for all $t$. Moreover $P$ is nondegenerate if and only if the only $\xi$-loop $\eta$ with $A_P\eta=0$ is $\eta=0$.
--
--   **Formalization Note** The first claim is stated for every `Φ` with `IsLinReebFlow P Φ`.
-- source:
--   U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Definition 2.5; C. Wendl, Lectures on Symplectic Field Theory, lecture notes, Humboldt-Universität zu Berlin (2026 version); earlier version arXiv:1612.01009, Section 3.1

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- The kernel of the asymptotic operator: a `ξ`-loop `η` satisfies `A_P η = 0` if and only if
`η(t) = Φ(Tt) η(0)` for the linearized Reeb flow `Φ`. Consequently `P` is nondegenerate if and
only if `A_P` has trivial kernel on `ξ`-loops. -/
theorem asympOp_eq_zero_iff {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (P : ReebOrbit H) :
    (∀ Φ : ℝ → V n →L[ℝ] V n, IsLinReebFlow P Φ → ∀ η : ℝ → V n, IsXiLoop P η →
      ((∀ t : ℝ, asympOp J P η t = 0) ↔ ∀ t : ℝ, η t = Φ (P.T * t) (η 0))) ∧
    (P.IsNondegenerate ↔
      ∀ η : ℝ → V n, IsXiLoop P η → (∀ t : ℝ, asympOp J P η t = 0) → ∀ t : ℝ, η t = 0) := by
  sorry

end FiniteEnergyPlane
