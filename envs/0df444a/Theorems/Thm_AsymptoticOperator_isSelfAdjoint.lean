-- Prove2me | Theorems.Thm_AsymptoticOperator_isSelfAdjoint
-- name    : AsymptoticOperator.isSelfAdjoint
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-09T14:32:31.536004+00:00
-- url     : https://prove2.me/theorems/692683ce-e806-4241-ae55-3006d4b54d78
-- title:
--   The asymptotic operator of a symmetric loop is self-adjoint
-- statement:
--   Let $S:S^1\to\mathbb{R}^{2n\times2n}$ be continuous with $S(t)^{\mathsf T}=S(t)$ for all $t$. Then $A_S=-J_0\partial_t-S$ with domain $W^{1,2}(S^1,\mathbb{R}^{2n})$ is a self-adjoint operator on $L^2(S^1,\mathbb{R}^{2n})$: $A_S^*=A_S$, including equality of domains.
-- source:
--   Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, §3.4, Exercise 3.29, p. 61; Hofer-Wysocki-Zehnder, Properties of pseudoholomorphic curves in symplectisations II, GAFA 5 (1995) 270-328, https://doi.org/10.1007/BF01895669, Section 3, p. 285, after equation (35) (n = 1)

import Definitions.Def_AsymptoticOperator_Setting

namespace AsymptoticOperator

open ConleyZehnder

/-- Wendl §3.4, Exercise 3.29; Hofer–Wysocki–Zehnder (GAFA 1995), §3, p. 285 for `n = 1`: for a loop of symmetric matrices, `A_S` with domain
`W^{1,2}` is self-adjoint. -/
theorem isSelfAdjoint {n : ℕ} (S : C(UnitAddCircle, Mat n)) (hS : IsSymLoop S) :
    IsSelfAdjoint (asymptoticOperator S) := by sorry

end AsymptoticOperator
