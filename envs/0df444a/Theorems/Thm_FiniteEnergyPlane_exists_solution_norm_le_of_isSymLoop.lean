-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_solution_norm_le_of_isSymLoop
-- name    : FiniteEnergyPlane.exists_solution_norm_le_of_isSymLoop
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-21T15:49:50.140255+00:00
-- url     : https://prove2.me/theorems/f99f07b3-f184-4966-aa00-dd2073b6f0ed
-- title:
--   Solutions of the linear equation ζ' = J₀S(t)ζ for a symmetric loop: existence and two-sided growth bounds
-- statement:
--   Let $S : \mathbb{R} \to \mathbb{R}^{2 \times 2}$ be a continuous $1$-periodic loop of symmetric matrices, and consider the linear equation $\zeta'(t) = J_0 S(t)\,\zeta(t)$ on $\mathbb{R}^2$, with $J_0 = \begin{pmatrix} 0 & -1 \\ 1 & 0 \end{pmatrix}$. Let $\Lambda \ge 0$. Then:
--   - for every $t_0 \in \mathbb{R}$ and $a_0 \in \mathbb{R}^2$ there is a solution $\zeta$ on $\mathbb{R}$ with $\zeta(t_0) = a_0$;
--   - there is $C \ge 1$ such that every solution satisfies $\|\zeta(t_0 + s)\| \le C\,\|\zeta(t_0)\|$ and $\|\zeta(t_0)\| \le C\,\|\zeta(t_0 + s)\|$ for all $t_0 \in \mathbb{R}$ and $|s| \le \Lambda$.
--
--   Role: existence of solutions through any point, and size comparison of a solution at times a bounded distance apart, uniformly in the base time.
--
--   Formalization Note: `CauchyRiemannIndex.IsSymLoop S` means $S$ is continuous, $1$-periodic and pointwise symmetric. Vectors live in `CauchyRiemannIndex.Vec 1` (Euclidean $\mathbb{R}^2$) and matrices act by `Matrix.toEuclideanLin`.
-- source:
--   Standard (linear ODE theory, Grönwall's inequality)

import Definitions.Def_CauchyRiemannIndex_Setting

namespace FiniteEnergyPlane

/-- Solutions of `ζ' = J₀ S(t) ζ` for a loop `S` of symmetric `2 × 2` matrices (continuous and
`1`-periodic). Every initial value `ζ(t₀) = a₀` has a solution on `ℝ`, and for each `Λ ≥ 0` there
is `C ≥ 1` such that every solution satisfies `‖ζ(t₀ + s)‖ ≤ C ‖ζ(t₀)‖` and
`‖ζ(t₀)‖ ≤ C ‖ζ(t₀ + s)‖` whenever `|s| ≤ Λ`. -/
theorem exists_solution_norm_le_of_isSymLoop (S : ℝ → CauchyRiemannIndex.Mat 1)
    (hS : CauchyRiemannIndex.IsSymLoop S) (Λ : ℝ) (hΛ : 0 ≤ Λ) :
    ∃ C : ℝ, 1 ≤ C ∧
      (∀ (t₀ : ℝ) (a₀ : CauchyRiemannIndex.Vec 1), ∃ ζ : ℝ → CauchyRiemannIndex.Vec 1,
        (∀ t, HasDerivAt ζ (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1 * S t) (ζ t)) t) ∧
        ζ t₀ = a₀) ∧
      ∀ ζ : ℝ → CauchyRiemannIndex.Vec 1,
        (∀ t, HasDerivAt ζ (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1 * S t) (ζ t)) t) →
        ∀ t₀ s : ℝ, |s| ≤ Λ → ‖ζ (t₀ + s)‖ ≤ C * ‖ζ t₀‖ ∧ ‖ζ t₀‖ ≤ C * ‖ζ (t₀ + s)‖ := by
  sorry

end FiniteEnergyPlane
