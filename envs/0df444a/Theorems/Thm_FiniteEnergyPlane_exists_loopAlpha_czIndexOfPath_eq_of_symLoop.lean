-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_loopAlpha_czIndexOfPath_eq_of_symLoop
-- name    : FiniteEnergyPlane.exists_loopAlpha_czIndexOfPath_eq_of_symLoop
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-06T14:18:40.086397+00:00
-- url     : https://prove2.me/theorems/983b9313-b643-40fc-a7b4-9f44ba49ef1d
-- title:
--   A smooth symmetric loop, possibly degenerate, has index $\alpha^- + \alpha^+$
-- statement:
--   Let $S_\infty$ be a smooth symmetric loop of $2 \times 2$ matrices, not assumed nondegenerate. Then there are integers $a, b$ with $b \in \{a, a + 1\}$ such that $a$ is the largest winding number of a negative eigenvalue of $-J_0 \partial_t - S_\infty$, $b$ is the smallest winding number of a nonnegative eigenvalue, and the fundamental solution $\Psi$ has `czIndexOfPath` equal to $a + b$.
--
--   **Role.** This extends the identity $\mu_{CZ} = \alpha^- + \alpha^+$ to degenerate loops, with the lower semicontinuous index, so results on winding windows apply without a nondegeneracy assumption.
--
--   **Formalization Note.** The extremal properties are stated through `HasLoopEigenWind`.
-- source:
--   H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectizations II (1995), Section 3; U. Hryniewicz, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Section 2.1.1

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open scoped ContDiff Real

/-- For a smooth symmetric loop `S∞`, not necessarily nondegenerate, there are integers `a, b` with
`b ∈ {a, a + 1}` such that `a` is the largest winding number of a negative eigenvalue of
`-J₀ ∂ₜ - S∞`, `b` is the smallest winding number of a nonnegative eigenvalue, and the fundamental
solution has `czIndexOfPath` equal to `a + b`. -/
theorem exists_loopAlpha_czIndexOfPath_eq_of_symLoop (Sinf : ℝ → CauchyRiemannIndex.Mat 1)
    (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j)) :
    ∃ a b : ℤ,
      ((∃ μ < 0, HasLoopEigenWind Sinf μ a) ∧
        ∀ μ < 0, ∀ k : ℤ, HasLoopEigenWind Sinf μ k → k ≤ a) ∧
      ((∃ μ, 0 ≤ μ ∧ HasLoopEigenWind Sinf μ b) ∧
        ∀ μ, 0 ≤ μ → ∀ k : ℤ, HasLoopEigenWind Sinf μ k → b ≤ k) ∧
      (b = a ∨ b = a + 1) ∧
      ∀ Ψ : ℝ → CauchyRiemannIndex.Mat 1, CauchyRiemannIndex.IsFundamentalSolution Sinf Ψ →
        HryniewiczCriterion.czIndexOfPath
          (fun τ => Matrix.reindex finSumFinEquiv finSumFinEquiv (Ψ τ)) = a + b := by
  sorry

end FiniteEnergyPlane
