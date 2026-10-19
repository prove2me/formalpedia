-- Prove2me | Theorems.Thm_CauchyRiemannIndex_simplyConnectedSpace_nonzero_of_three_le_card
-- name    : CauchyRiemannIndex.simplyConnectedSpace_nonzero_of_three_le_card
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-16T18:03:00.257041+00:00
-- url     : https://prove2.me/theorems/a5de3223-54ef-4f04-a3a4-c7829b5c1946
-- title:
--   $\mathbb R^m\setminus\{0\}$ is simply connected for $m\ge3$
-- statement:
--   Let $\iota$ be a finite set with at least three elements. Then the punctured space
--   $$\mathbb R^\iota\setminus\{0\}$$
--   is simply connected: it is nonempty, path-connected, and every loop in it is null-homotopic relative to its base point.
--
--   This is the case $m\ge3$ of the classical computation of the fundamental group of $\mathbb R^m\setminus\{0\}$, stated for coordinate spaces $\mathbb R^\iota$ indexed by an arbitrary finite type so that it applies directly to spaces such as $\mathbb R^{2n}$ indexed by `Fin n ⊕ Fin n`.
--
--   **Formalization Note.** $\mathbb R^\iota$ is the function space `ι → ℝ` with its product topology, for `[Fintype ι]` with `3 ≤ Fintype.card ι`; the punctured space is the subtype `{y : ι → ℝ // y ≠ 0}` with the subspace topology, and simple connectivity is Mathlib's `SimplyConnectedSpace`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 3, §3.4, p. 62 (auxiliary fact for Theorem 3.34); A. Hatcher, Algebraic Topology, Cambridge University Press, 2002, Proposition 1.14 ($\pi_1(S^n)=0$ for $n\ge2$)

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

namespace CauchyRiemannIndex

/-- If `ι` has at least three elements, the punctured space `ℝ^ι ∖ {0}` is simply connected. -/
theorem simplyConnectedSpace_nonzero_of_three_le_card {ι : Type*} [Fintype ι]
    (hι : 3 ≤ Fintype.card ι) : SimplyConnectedSpace {y : ι → ℝ // y ≠ 0} := by sorry

end CauchyRiemannIndex
