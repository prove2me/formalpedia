-- Prove2me | Theorems.Thm_AsymptoticOperator_hasDiscreteEigenbasis
-- name    : AsymptoticOperator.hasDiscreteEigenbasis
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-09T14:32:44.426967+00:00
-- url     : https://prove2.me/theorems/c71b1fa7-53d0-44d6-9539-899ae33a1fd4
-- title:
--   The asymptotic operator has an orthonormal eigenbasis with discrete spectrum
-- statement:
--   Let $S:S^1\to\mathbb{R}^{2n\times2n}$ be continuous with $S(t)^{\mathsf T}=S(t)$ for all $t$. There are an orthonormal basis $(e_i)_{i\in I}$ of $L^2(S^1,\mathbb{R}^{2n})$ and real numbers $(\lambda_i)_{i\in I}$ such that every $e_i$ lies in $W^{1,2}$, $A_Se_i=\lambda_ie_i$, and for every $c\ge0$ only finitely many $i$ satisfy $|\lambda_i|\le c$.
--
--   In particular the spectrum of $A_S$ consists of real eigenvalues of finite multiplicity, accumulating only at $\pm\infty$.
-- source:
--   Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, §3.2, p. 46; Hofer-Wysocki-Zehnder, Properties of pseudoholomorphic curves in symplectisations II, GAFA 5 (1995) 270-328, https://doi.org/10.1007/BF01895669, Section 3, p. 285, after equation (35) (n = 1)

import Definitions.Def_AsymptoticOperator_Setting

namespace AsymptoticOperator

open ConleyZehnder

/-- Wendl §3.2, p. 46; Hofer–Wysocki–Zehnder (GAFA 1995), §3, p. 285 for `n = 1`: `L²(S¹, ℝ²ⁿ)` has an orthonormal basis of
eigenvectors of `A_S`; the eigenvalues are real, have finite multiplicity and
accumulate only at `±∞`. -/
theorem hasDiscreteEigenbasis {n : ℕ} (S : C(UnitAddCircle, Mat n)) (hS : IsSymLoop S) :
    HasDiscreteEigenbasis (asymptoticOperator S) := by sorry

end AsymptoticOperator
