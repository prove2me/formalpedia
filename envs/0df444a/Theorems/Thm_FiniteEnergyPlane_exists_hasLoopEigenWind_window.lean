-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_hasLoopEigenWind_window
-- name    : FiniteEnergyPlane.exists_hasLoopEigenWind_window
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-06T13:39:28.806824+00:00
-- url     : https://prove2.me/theorems/1f1e80cf-cf32-4cd4-b183-57d2ca4e74a3
-- title:
--   A weight below zero separating eigenvalues of winding at most one from winding at least two
-- statement:
--   Let $S_\infty$ be a smooth symmetric loop of $2 \times 2$ matrices, not assumed nondegenerate, and let $\Psi$ be its fundamental solution. Suppose the Conley–Zehnder index of $\Psi$ (`czIndexOfPath`, the lower semicontinuous extension to degenerate paths) is at least $3$.
--
--   Then there is $\delta < 0$ which is not an eigenvalue of $-J_0 \partial_t - S_\infty$, such that every eigenvalue $\mu < \delta$ has winding number at most $1$ and every eigenvalue $\mu > \delta$ has winding number at least $2$.
--
--   **Role.** This is a spectral gap below $0$ separating winding numbers $\le 1$ from winding numbers $\ge 2$. It is the choice of exponential weight for operators along fast finite-energy planes, and it holds also for degenerate asymptotic orbits.
--
--   **Formalization Note.** "Eigenvalue $\mu$ with winding number $k$" is `HasLoopEigenWind Sinf μ k`, and "not an eigenvalue" is `∀ e, ¬ IsLoopEigen Sinf δ e`.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076, Section 6 (the weight δ of (87)); H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectizations II (1995), Section 3

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open scoped ContDiff

/-- Let `S∞` be a smooth symmetric loop, not necessarily nondegenerate, whose fundamental solution
has Conley–Zehnder index at least `3` in the sense of `czIndexOfPath`. Then there is `δ < 0` which
is not an eigenvalue of `-J₀ ∂ₜ - S∞`, such that every eigenvalue below `δ` has winding number at
most `1` and every eigenvalue above `δ` has winding number at least `2`. -/
theorem exists_hasLoopEigenWind_window (Sinf : ℝ → CauchyRiemannIndex.Mat 1)
    (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (Ψ : ℝ → CauchyRiemannIndex.Mat 1) (hΨ : CauchyRiemannIndex.IsFundamentalSolution Sinf Ψ)
    (hcz : 3 ≤ HryniewiczCriterion.czIndexOfPath
      (fun τ => Matrix.reindex finSumFinEquiv finSumFinEquiv (Ψ τ))) :
    ∃ δ < 0, (∀ e, ¬ IsLoopEigen Sinf δ e) ∧
      ∀ (μ : ℝ) (k : ℤ), HasLoopEigenWind Sinf μ k → (μ < δ ∧ k ≤ 1) ∨ (δ < μ ∧ 2 ≤ k) := by
  sorry

end FiniteEnergyPlane
