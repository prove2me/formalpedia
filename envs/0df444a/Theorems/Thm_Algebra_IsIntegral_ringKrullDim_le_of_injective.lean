-- Prove2me | Theorems.Thm_Algebra_IsIntegral_ringKrullDim_le_of_injective
-- name    : Algebra.IsIntegral.ringKrullDim_le_of_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/93147343-9f61-5599-9a6b-da295037ead1
-- title:
--   Krull dimension grows along injective integral extensions
-- statement:
--   Let $R$ and $S$ be commutative rings and let $S$ be an $R$-algebra which is integral over $R$, i.e. every element of $S$ satisfies a monic polynomial with coefficients in $R$. Assume the structure map $\mathrm{algebraMap}\colon R \to S$ is injective. Then the Krull dimension of $R$ is at most the Krull dimension of $S$, as an inequality in $\mathbb{Z} \cup \{\pm\infty\}$ (`ringKrullDim` takes values in `WithBot (WithTop ℕ)`, with the value $-\infty$ assigned to the zero ring). The inequality is thus stated for arbitrary, not necessarily Noetherian or finite, integral extensions, and includes the degenerate cases: if $R$ is the zero ring its dimension is $-\infty$ and the inequality is automatic, while injectivity forces $S$ to be nontrivial whenever $R$ is.
--
--   This is the dimension-theoretic consequence of the Cohen–Seidenberg lying-over and going-up theorems for integral extensions: chains of primes of $R$ lift to chains of the same length in $S$. It is used in the project wherever a lower bound on the dimension of a ring has to be transported along a finite injective cover, for instance in the analysis of stalks and regular local rings on integral models of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_IsIntegral_ringKrullDim_le_of_injective.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Algebra.IsIntegral.ringKrullDim_le_of_injective
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]
    (hinj : Function.Injective (algebraMap R S)) :
    ringKrullDim R ≤ ringKrullDim S := by sorry
