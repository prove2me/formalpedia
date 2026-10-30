-- Prove2me | Theorems.Thm_CauchyRiemannIndex_isNondegenerate_smul_comp_affine
-- name    : CauchyRiemannIndex.isNondegenerate_smul_comp_affine
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-29T21:53:30.897391+00:00
-- url     : https://prove2.me/theorems/ff704ef3-389d-45f6-bb2a-876815698dde
-- title:
--   Nondegeneracy of an asymptotic operator under shift and reversal of the loop
-- statement:
--   Let $S_\infty$ be a continuous $1$-periodic loop of symmetric real $2n\times2n$ matrices such that the asymptotic operator $-J_0\partial_t-S_\infty$ is nondegenerate. Then for $\varepsilon=\pm1$ and every $c\in\mathbb{R}$ the loop $t\mapsto\varepsilon S_\infty(\varepsilon t+c)$ is again a continuous $1$-periodic loop of symmetric matrices, and its asymptotic operator $-J_0\partial_t-\varepsilon S_\infty(\varepsilon t+c)$ is nondegenerate.
--
--   For $\varepsilon=1$ this is the invariance of nondegeneracy under a shift of the time parameter; for $\varepsilon=-1$ the loop is also traversed backwards, which is how the asymptotic operator of a negative puncture appears.
--
--   **Formalization Note** `Mat n` and `Vec n` are $2n\times2n$ real matrices and $\mathbb{R}^{2n}$, `crOp S ζ` is $\partial_s\zeta+J_0\partial_t\zeta+S\zeta$, a loop of symmetric matrices is `IsSymLoop` (continuous, $1$-periodic, symmetric), and nondegeneracy of $-J_0\partial_t-S_\infty$ is `CauchyRiemannIndex.IsNondegenerate` ($1$ is not an eigenvalue of the time-$1$ map $\Psi(1)$ of $\Psi'=J_0S_\infty\Psi$, $\Psi(0)=1$).
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory (2026 notes), §3.5; used for U. Hryniewicz, J. Symplectic Geom. 12 (2014), Theorem 2.10

import Definitions.Def_CauchyRiemannIndex_Setting

namespace CauchyRiemannIndex

open Matrix

/-- If `S∞` is a loop of symmetric matrices whose asymptotic operator `-J₀ ∂ₜ - S∞` is
nondegenerate, then for `ε = ±1` and any `c` the loop `t ↦ ε S∞(εt + c)` (shifted, and reversed
when `ε = -1`) is again a loop of symmetric matrices with nondegenerate asymptotic operator. -/
theorem isNondegenerate_smul_comp_affine (n : ℕ) (Sinf : ℝ → Mat n) (hS : IsSymLoop Sinf)
    (hnd : IsNondegenerate Sinf) (ε c : ℝ) (hε : ε = 1 ∨ ε = -1) :
    IsSymLoop (fun t => ε • Sinf (ε * t + c)) ∧ IsNondegenerate (fun t => ε • Sinf (ε * t + c)) := by
  sorry

end CauchyRiemannIndex
