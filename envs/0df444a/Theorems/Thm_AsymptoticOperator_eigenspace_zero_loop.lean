-- Prove2me | Theorems.Thm_AsymptoticOperator_eigenspace_zero_loop
-- name    : AsymptoticOperator.eigenspace_zero_loop
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-09T14:33:51.477625+00:00
-- url     : https://prove2.me/theorems/2a158964-4dcd-4ed3-9aa6-6194bcd44983
-- title:
--   Spectrum of the unperturbed operator $-J_0\partial_t$
-- statement:
--   For $S=0$, $\mu\in\mathbb{R}$ is an eigenvalue of $A_0=-J_0\partial_t$ if and only if $\mu=2\pi k$ for some $k\in\mathbb{Z}$, and then the eigenspace $\ker(A_0-\mu)$ is linearly isomorphic to $\mathbb{R}^{2n}$. For every other $\mu$ the eigenspace is $\{0\}$.
-- source:
--   Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, §3.4, p. 63; Hofer-Wysocki-Zehnder, Properties of pseudoholomorphic curves in symplectisations II, GAFA 5 (1995) 270-328, https://doi.org/10.1007/BF01895669, Section 3, p. 287 (n = 1)

import Definitions.Def_AsymptoticOperator_Setting

namespace AsymptoticOperator

open ConleyZehnder

/-- Wendl §3.4, p. 63; Hofer–Wysocki–Zehnder (GAFA 1995), §3, p. 287 for `n = 1`: for `S = 0` the eigenvalues of `A_0 = -J₀ ∂ₜ` are
exactly `2πk`, `k ∈ ℤ`, each with a `2n`-dimensional eigenspace. -/
theorem eigenspace_zero_loop (n : ℕ) (μ : ℝ) :
    ((∃ k : ℤ, μ = 2 * Real.pi * k) →
        Nonempty (eigenspace (asymptoticOperator (0 : C(UnitAddCircle, Mat n))) μ ≃ₗ[ℝ]
          (Fin n ⊕ Fin n → ℝ))) ∧
      ((∀ k : ℤ, μ ≠ 2 * Real.pi * k) →
        eigenspace (asymptoticOperator (0 : C(UnitAddCircle, Mat n))) μ = ⊥) := by sorry

end AsymptoticOperator
