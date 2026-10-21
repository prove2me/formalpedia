-- Prove2me | Theorems.Thm_CauchyRiemannIndex_isNondegenerate_pi_smul_one
-- name    : CauchyRiemannIndex.isNondegenerate_pi_smul_one
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-20T15:43:42.113946+00:00
-- url     : https://prove2.me/theorems/d70712f0-371e-4b7c-ac24-1b442d4ee914
-- title:
--   The constant loop π·Id gives a nondegenerate asymptotic operator in every dimension
-- statement:
--   Let $m\ge0$. The constant loop $S_\infty(t)=\pi\,\mathrm{Id}$ on $\mathbb{R}^{2m}$ is a continuous $1$-periodic loop of symmetric matrices, and its asymptotic operator $-J_0\partial_t-\pi$ is nondegenerate: the fundamental solution $\Psi$ of $\Psi'=J_0\pi\Psi$, $\Psi(0)=\mathrm{Id}$, has no eigenvalue $1$ at $t=1$.
--
--   This gives a nondegenerate reference loop in every dimension.
--
--   **Formalization Note** Loops are `IsSymLoop` and nondegeneracy is `IsNondegenerate` (for every fundamental solution $\Psi$, $\det(\mathrm{Id}-\Psi(1))\neq0$), from the setting module.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 3, §3.4 (nondegenerate asymptotic operators)

import Definitions.Def_CauchyRiemannIndex_Setting

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- The constant loop `S∞ ≡ π · Id` on `ℝ^{2m}` is a loop of symmetric matrices whose asymptotic
operator `-J₀ ∂ₜ - π` is nondegenerate. -/
theorem isNondegenerate_pi_smul_one (m : ℕ) :
    IsSymLoop (fun _ : ℝ => Real.pi • (1 : Mat m)) ∧
      IsNondegenerate (fun _ : ℝ => Real.pi • (1 : Mat m)) := by
  sorry

end CauchyRiemannIndex
