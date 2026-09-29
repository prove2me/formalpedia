-- Prove2me | Theorems.Thm_Algebra_FormallyUnramified_nonempty_ringHom_int
-- name    : Algebra.FormallyUnramified.nonempty_ringHom_int
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/d94a2f65-fbb1-588f-b972-d497e394b2c2
-- title:
--   A nonzero finite flat unramified ℤ-algebra has a ℤ-point
-- statement:
--   Let $B$ be a commutative ring which is nontrivial (so $0 \neq 1$ in $B$), which is finite as a $\mathbb{Z}$-module, flat as a $\mathbb{Z}$-module, and formally unramified over $\mathbb{Z}$ in the sense of Mathlib's `Algebra.FormallyUnramified` (the relative cotangent module, equivalently the module of Kähler differentials $\Omega_{B/\mathbb{Z}}$, vanishes; here the $\mathbb{Z}$-algebra structure is the canonical one on any ring). Taken together these hypotheses say that $B$ is a nonzero finite étale $\mathbb{Z}$-algebra. The conclusion is that the type of ring homomorphisms $B \to \mathbb{Z}$ is nonempty, i.e. there exists at least one ring homomorphism $B \to \mathbb{Z}$; equivalently, the finite étale covering $\operatorname{Spec} B \to \operatorname{Spec} \mathbb{Z}$ admits a section. Only existence of a single such homomorphism is asserted; the stronger structural statement that $B$ is isomorphic to a finite product of copies of $\mathbb{Z}$ is not part of the conclusion.
--
--   This is the algebraic form of the assertion that $\operatorname{Spec}\mathbb{Z}$ is simply connected in the étale topology, $\pi_1^{\mathrm{et}}(\operatorname{Spec}\mathbb{Z}) = 1$, in the weak shape 'every nonzero finite étale $\mathbb{Z}$-algebra has a $\mathbb{Z}$-point'. It is used in the descent-theoretic parts of the development, namely in the computation of Amitsur-trivial fppf covers for the constant $\mathbb{Z}/n$ sheaf and in the production of complete orthogonal idempotents from a faithfully flat base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_FormallyUnramified_nonempty_ringHom_int.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Algebra.FormallyUnramified.nonempty_ringHom_int
    (B : Type*) [CommRing B] [Nontrivial B] [Module.Finite ℤ B] [Module.Flat ℤ B]
    [Algebra.FormallyUnramified ℤ B] : Nonempty (B →+* ℤ) := by sorry
