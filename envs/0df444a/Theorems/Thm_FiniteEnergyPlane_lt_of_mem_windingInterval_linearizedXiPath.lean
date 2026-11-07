-- Prove2me | Theorems.Thm_FiniteEnergyPlane_lt_of_mem_windingInterval_linearizedXiPath
-- name    : FiniteEnergyPlane.lt_of_mem_windingInterval_linearizedXiPath
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-06T14:27:30.612348+00:00
-- url     : https://prove2.me/theorems/3b43ad98-98e4-41e2-8a03-a3dfb91cc926
-- title:
--   Winding thresholds pass from the linearized flow of a Reeb orbit to its frame loop
-- statement:
--   Let $Q$ be a periodic Reeb orbit, possibly degenerate, and $P$ the corresponding Hamiltonian orbit with the same starting point and with action equal to the period of $Q$. Let $Z$ be a unitary frame of $\xi$ along $Q$ whose loop windings agree with those in the global frame, $S_\infty$ the loop representing $A_Q$ in that frame, and $\Psi$ its fundamental solution.
--
--   If every element of the winding interval of the linearized path of $P$ is greater than the integer $k$, then every element of the winding interval of $\Psi$ is greater than $k$.
--
--   **Role.** Lower bounds on the Conley–Zehnder index in the global frame transfer to the matrix loop of the asymptotic operator, including for degenerate orbits, where the equality `czIndexOfPath_linearizedXiPath_eq` is not available.
--
--   **Formalization Note.** The linearized path is `HryniewiczCriterion.linearizedXiPath`; the frame hypothesis is the `hwind` equivalence between `HasXiLoopWind` and `HasLoopWind`.
-- source:
--   U. Hryniewicz, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Section 2.1.1

import Definitions.Def_FiniteEnergyPlane_Compactness
import Mathlib.Topology.Instances.Matrix

namespace FiniteEnergyPlane

open scoped ContDiff Real

/-- Let `Q` be a Reeb orbit, possibly degenerate, and `P` the corresponding Hamiltonian orbit, with the
same starting point and action. Let `Z` be a unitary frame along `Q` whose loop windings agree with
those in the global frame, `S∞` the loop of `A_Q` in that frame and `Ψ` its fundamental solution. If
every element of the winding interval of the linearized path of `P` is greater than the integer `k`,
then every element of the winding interval of `Ψ` is greater than `k`. -/
theorem lt_of_mem_windingInterval_linearizedXiPath (H : V 1 → ℝ) (hH₀ : HryniewiczCriterion.IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (P : HryniewiczCriterion.PeriodicOrbit H) (Q : ReebOrbit H)
    (hT : Q.T = ∫ τ in (0 : ℝ)..P.T, liouville (n := 1) (P.x τ) (deriv P.x τ))
    (h0 : Q.x 0 = P.x 0)
    (Z : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1) (hZ : IsUnitaryXiFrame J Q Z)
    (hwind : ∀ ζ : ℝ → CauchyRiemannIndex.Vec 1, Continuous ζ → Function.Periodic ζ 1 →
        (∀ t : ℝ, ζ t ≠ 0) → ∀ k : ℤ,
          (HasXiLoopWind Q (fun t => Z t (ζ t)) k ↔ HasLoopWind (fun t => vecToC (ζ t)) k))
    (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (hSym : CauchyRiemannIndex.IsSymLoop Sinf)
    (hA : ∀ η : ℝ → CauchyRiemannIndex.Vec 1, ContDiff ℝ ∞ η → Function.Periodic η 1 →
        ∀ t : ℝ, asympOp J Q (fun t => Z t (η t)) t =
          Z t (-(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) (deriv η t)) -
            Matrix.toEuclideanLin (Sinf t) (η t)))
    (Ψ : ℝ → CauchyRiemannIndex.Mat 1) (hΨ : CauchyRiemannIndex.IsFundamentalSolution Sinf Ψ)
    (Y : ℝ → (HryniewiczCriterion.R4 →L[ℝ] HryniewiczCriterion.R4))
    (hY : HryniewiczCriterion.IsLinearizedFlow H P.x Y) (k : ℤ)
    (hk : ∀ d ∈ HryniewiczCriterion.windingInterval (HryniewiczCriterion.linearizedXiPath H P Y),
      (k : ℝ) < d) :
    ∀ d ∈ HryniewiczCriterion.windingInterval
      (fun τ => Matrix.reindex finSumFinEquiv finSumFinEquiv (Ψ τ)), (k : ℝ) < d := by
  sorry

end FiniteEnergyPlane
