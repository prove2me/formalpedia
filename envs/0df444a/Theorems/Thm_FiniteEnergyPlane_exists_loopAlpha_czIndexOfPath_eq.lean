-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_loopAlpha_czIndexOfPath_eq
-- name    : FiniteEnergyPlane.exists_loopAlpha_czIndexOfPath_eq
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-02T16:24:31.230513+00:00
-- url     : https://prove2.me/theorems/288c2642-92ca-4f56-aa04-b0af2c4457eb
-- title:
--   The Conley–Zehnder index of a nondegenerate loop operator equals $\alpha^-+\alpha^+$
-- statement:
--   Let $S_\infty:\mathbb{R}\to\mathbb{R}^{2\times 2}$ be a smooth $1$-periodic loop of symmetric matrices, and suppose the asymptotic operator $A=-J_0\,\partial_t-S_\infty$ on $1$-periodic loops in $\mathbb{R}^2=\mathbb{C}$ is nondegenerate, i.e. $0$ is not an eigenvalue. Let $\Psi$ be the fundamental solution, $\Psi(0)=I$, $\Psi'(t)=J_0S_\infty(t)\Psi(t)$. Then:
--
--   1. $\alpha^-$, the largest winding number of the eigenfunctions of a negative eigenvalue of $A$, exists;
--   2. $\alpha^+$, the smallest winding number of the eigenfunctions of a nonnegative eigenvalue of $A$, exists;
--   3. $\alpha^+-\alpha^-\in\{0,1\}$;
--   4. the Conley–Zehnder index (Hryniewicz's winding-interval index) of the path $t\mapsto\Psi(t)$, $t\in[0,1]$, equals $\alpha^-+\alpha^+$.
--
--   This is the loop form of Hofer–Wysocki–Zehnder's formula $\mu_{CZ}=2\alpha^-+p$ with $p=\alpha^+-\alpha^-$: it expresses the Conley–Zehnder index of a nondegenerate asymptotic operator in dimension two through the winding numbers of its eigenfunctions.
--
--   **Formalization Note** "$\mu$ is an eigenvalue whose eigenfunctions have winding $k$" is `HasLoopEigenWind Sinf μ k` (winding of $t\mapsto e(t)$ as a loop in $\mathbb{C}$ via `vecToC`). $\alpha^\pm$ are spelled out as an attained upper (resp. lower) bound. Nondegeneracy is `CauchyRiemannIndex.IsNondegenerate`, the index is `HryniewiczCriterion.czIndexOfPath`, and matrices are transported along `finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2` ($q\mapsto0$, $p\mapsto1$).
-- source:
--   H. Hofer, K. Wysocki, E. Zehnder, GAFA 5 (1995), Theorem 3.10; U. Hryniewicz, J. Symplectic Geom. 12 (2014), Remark 2.6 (auxiliary lemma)

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Hofer–Wysocki–Zehnder (GAFA 1995, Theorem 3.10) for a loop of symmetric `2 × 2` matrices: if
`A = -J₀ ∂ₜ - S∞` is nondegenerate, then `a = α⁻` (the largest winding number of a negative
eigenvalue) and `b = α⁺` (the smallest winding number of a nonnegative eigenvalue) exist,
`b - a ∈ {0, 1}`, and Hryniewicz's index of the path `t ↦ Ψ(t)`, `t ∈ [0, 1]`, of the fundamental
solution `Ψ` of `S∞` is `a + b`. The matrices are transported along `Fin 1 ⊕ Fin 1 ≃ Fin 2`. -/
theorem exists_loopAlpha_czIndexOfPath_eq (Sinf : ℝ → CauchyRiemannIndex.Mat 1)
    (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (hnd : CauchyRiemannIndex.IsNondegenerate Sinf) :
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
