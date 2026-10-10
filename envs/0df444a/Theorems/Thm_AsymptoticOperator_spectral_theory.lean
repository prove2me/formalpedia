-- Prove2me | Theorems.Thm_AsymptoticOperator_spectral_theory
-- name    : AsymptoticOperator.spectral_theory
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-09T14:35:34.39352+00:00
-- url     : https://prove2.me/theorems/af70d731-03d5-49ce-8cab-6fb42b53b6ff
-- title:
--   Spectral theory of asymptotic operators on the circle
-- statement:
--   Let $S:S^1\to\mathbb{R}^{2n\times2n}$ be continuous with $S(t)^{\mathsf T}=S(t)$ for all $t$, and let $A_S=-J_0\partial_t-S$ with domain $W^{1,2}(S^1,\mathbb{R}^{2n})$. Then:
--
--   1. $A_S$ is self-adjoint on $L^2(S^1,\mathbb{R}^{2n})$;
--   2. $L^2(S^1,\mathbb{R}^{2n})$ has an orthonormal basis of eigenvectors of $A_S$ in $W^{1,2}$, with real eigenvalues of finite multiplicity accumulating only at $\pm\infty$;
--   3. for the fundamental solution $\Psi$ ($\Psi(0)=\mathrm{Id}$, $\Psi'=J_0S\Psi$), $\ker A_S\cong\ker(\Psi(1)-\mathrm{Id})$.
--
--   These are the basic analytic properties of the operator through which periodic orbits enter the Fredholm theory of Cauchy–Riemann operators.
-- source:
--   Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, §3.2, equation (3.4), p. 46; §3.4, Exercise 3.29 and p. 61; Hofer-Wysocki-Zehnder, Properties of pseudoholomorphic curves in symplectisations II, GAFA 5 (1995) 270-328, https://doi.org/10.1007/BF01895669, Section 3, p. 285, equation (35) and the paragraph after it (n = 1)

import Definitions.Def_AsymptoticOperator_Setting

namespace AsymptoticOperator

open ConleyZehnder

/-- Spectral theory of the asymptotic operator: for a loop `S` of symmetric matrices,
`A_S = -J₀ ∂ₜ - S` with domain `W^{1,2}` is self-adjoint, `L²(S¹, ℝ²ⁿ)` has an
orthonormal eigenbasis whose real eigenvalues have finite multiplicity and accumulate
only at `±∞`, and `ker A_S ≅ ker(Ψ(1) - Id)` for the fundamental solution `Ψ`. -/
theorem spectral_theory {n : ℕ} (S : C(UnitAddCircle, Mat n)) (hS : IsSymLoop S) :
    IsSelfAdjoint (asymptoticOperator S) ∧ HasDiscreteEigenbasis (asymptoticOperator S) ∧
      ∀ Ψ : ℝ → Mat n, IsFundamentalSolution S Ψ →
        Nonempty (eigenspace (asymptoticOperator S) 0 ≃ₗ[ℝ]
          LinearMap.ker (Matrix.toLin' (Ψ 1 - 1))) := by sorry

end AsymptoticOperator
