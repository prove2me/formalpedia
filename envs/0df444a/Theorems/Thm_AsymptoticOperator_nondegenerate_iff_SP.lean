-- Prove2me | Theorems.Thm_AsymptoticOperator_nondegenerate_iff_SP
-- name    : AsymptoticOperator.nondegenerate_iff_SP
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-09T14:35:18.028105+00:00
-- url     : https://prove2.me/theorems/e2cac0af-9e10-45c4-8a1e-318d6b7638d9
-- title:
--   An asymptotic operator is nondegenerate exactly when its fundamental solution lies in $\mathrm{SP}(n)$
-- statement:
--   Let $S:S^1\to\mathbb{R}^{2n\times2n}$ be continuous with $S(t)^{\mathsf T}=S(t)$ for all $t$, let $\Psi$ be its fundamental solution, and let $\psi=\Psi|_{[0,1]}$. Then $0$ is not an eigenvalue of $A_S$ if and only if $\psi\in\mathrm{SP}(n)$, i.e. $\psi$ is a path of symplectic matrices from $\mathrm{Id}$ to a matrix without eigenvalue $1$.
--
--   So nondegenerate asymptotic operators are exactly those whose fundamental solution has a Conley–Zehnder index $\mu_{CZ}(\psi)$ in the sense of `ConleyZehnder_Setting`.
-- source:
--   Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, §3.4, p. 61 (informal there); Hofer-Wysocki-Zehnder, Properties of pseudoholomorphic curves in symplectisations II, GAFA 5 (1995) 270-328, https://doi.org/10.1007/BF01895669, Section 3, p. 288, after Definition 3.9 (n = 1)

import Definitions.Def_AsymptoticOperator_Setting

namespace AsymptoticOperator

open ConleyZehnder

/-- `A_S` is nondegenerate (`0` is not an eigenvalue) if and only if the
fundamental solution restricted to `[0, 1]` lies in `SP(n)`, the domain of the
Conley–Zehnder index. -/
theorem nondegenerate_iff_SP {n : ℕ} (S : C(UnitAddCircle, Mat n)) (hS : IsSymLoop S)
    (Ψ : ℝ → Mat n) (hΨ : IsFundamentalSolution S Ψ) (ψ : C(unitInterval, Mat n))
    (hψ : ∀ t : unitInterval, ψ t = Ψ t) :
    eigenspace (asymptoticOperator S) 0 = ⊥ ↔ ψ ∈ SP n := by sorry

end AsymptoticOperator
