-- Prove2me | Theorems.Thm_AsymptoticOperator_kernel_equiv
-- name    : AsymptoticOperator.kernel_equiv
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-09T14:35:00.660931+00:00
-- url     : https://prove2.me/theorems/9461b9a0-c938-4593-9c0a-6e72fdb4cd10
-- title:
--   The kernel of the asymptotic operator is isomorphic to $\ker(\Psi(1)-\mathrm{Id})$
-- statement:
--   Let $S:S^1\to\mathbb{R}^{2n\times2n}$ be continuous with $S(t)^{\mathsf T}=S(t)$ for all $t$, and let $\Psi$ be its fundamental solution. Then the kernel of $A_S$ on $W^{1,2}(S^1,\mathbb{R}^{2n})$ is linearly isomorphic to
--   $$\ker\big(\Psi(1)-\mathrm{Id}\big)\subset\mathbb{R}^{2n}.$$
-- source:
--   Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, §3.4, p. 61 (informal there)

import Definitions.Def_AsymptoticOperator_Setting

namespace AsymptoticOperator

open ConleyZehnder

/-- Wendl §3.4, p. 61: the kernel of `A_S` is isomorphic to the `1`-eigenspace
`ker(Ψ(1) - Id)` of the time-one map of the fundamental solution. -/
theorem kernel_equiv {n : ℕ} (S : C(UnitAddCircle, Mat n)) (hS : IsSymLoop S)
    (Ψ : ℝ → Mat n) (hΨ : IsFundamentalSolution S Ψ) :
    Nonempty (eigenspace (asymptoticOperator S) 0 ≃ₗ[ℝ]
      LinearMap.ker (Matrix.toLin' (Ψ 1 - 1))) := by sorry

end AsymptoticOperator
