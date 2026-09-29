-- Prove2me | Theorems.Thm_Algebra_FormallyUnramified_of_isReduced_of_perfectField
-- name    : Algebra.FormallyUnramified.of_isReduced_of_perfectField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/93cd6aa3-b467-5c0e-a2c9-6ccaaa0ba05a
-- title:
--   Finite reduced algebras over a perfect field are formally unramified
-- statement:
--   Let $K$ be a field which is perfect, and let $B$ be a commutative ring equipped with the structure of a $K$-algebra, such that $B$ is finite as a $K$-module (i.e. finite-dimensional as a $K$-vector space) and $B$ is reduced (its only nilpotent element is $0$). The conclusion is that the algebra $B$ over $K$ is formally unramified in the sense of Mathlib: for every commutative ring $A$ and every ideal $I \subseteq A$ with $I^2 = 0$, any two $K$-algebra homomorphisms $B \to A$ that become equal after composition with $A \to A/I$ coincide; equivalently, the module of Kähler differentials $\Omega_{B/K}$ vanishes. No separability, connectedness or local hypothesis on $B$ is imposed beyond reducedness, and $K$ is only assumed perfect, not algebraically closed.
--
--   This is the standard statement that a finite reduced algebra over a perfect field is unramified (indeed étale) over that field; over an algebraically closed $K$ it amounts to $B \cong K^n$. It is used in the proof of [`HopfAlgebra.isCocomm_of_isReduced_baseChange_of_withConv_equiv`](thm.html#HopfAlgebra.isCocomm_of_isReduced_baseChange_of_withConv_equiv).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_FormallyUnramified_of_isReduced_of_perfectField.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Algebra.FormallyUnramified.of_isReduced_of_perfectField (K B : Type*) [Field K] [PerfectField K] [CommRing B] [Algebra K B] [Module.Finite K B] [IsReduced B] : Algebra.FormallyUnramified K B := by sorry
