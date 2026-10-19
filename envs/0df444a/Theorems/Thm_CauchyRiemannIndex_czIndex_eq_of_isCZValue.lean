-- Prove2me | Theorems.Thm_CauchyRiemannIndex_czIndex_eq_of_isCZValue
-- name    : CauchyRiemannIndex.czIndex_eq_of_isCZValue
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-17T11:15:26.442366+00:00
-- url     : https://prove2.me/theorems/b6bf6705-224f-43ef-9f7d-e1cff970b265
-- title:
--   A Conley–Zehnder value of a nondegenerate symplectic path is its index
-- statement:
--   Let $\psi:[0,1]\to\mathrm{Sp}(2n)$ be a continuous path of symplectic matrices with $\psi(0)=\mathrm{Id}$ and $\det(\mathrm{Id}-\psi(1))\neq0$. If $k\in\mathbb{Z}$ is a Conley–Zehnder value of $\psi$ (the degree of $\hat\rho^2$ along $\psi$ followed by some extension in $\mathrm{Sp}^*$ ending at $W^\pm$), then $\mu_{CZ}(\psi)=k$.
--
--   This lets one evaluate the mission's Conley–Zehnder index from any single admissible extension.
--
--   **Formalization Note** `IsCZValue ψ k` and `czIndex ψ` are the mission's definitions (Gutt, Definition 7 with Corollary 12); `czIndex` is defined by choice, so the statement says that this choice returns $k$.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 5, Lemma 5.29, p. 103

import Definitions.Def_CauchyRiemannIndex_Setting

namespace CauchyRiemannIndex

open Matrix

/-- For a path `ψ` of symplectic matrices with `ψ(0) = Id` and `1` not an eigenvalue of `ψ(1)`,
every Conley–Zehnder value `k` of `ψ` is its Conley–Zehnder index: `czIndex ψ = k`. -/
theorem czIndex_eq_of_isCZValue {n : ℕ} (ψ : C(unitInterval, Mat n))
    (hsymp : ∀ t, IsSymplectic (ψ t)) (h0 : ψ 0 = 1) (h1 : (1 - ψ 1).det ≠ 0) (k : ℤ)
    (hk : IsCZValue ψ k) : czIndex ψ = k := by
  sorry

end CauchyRiemannIndex
