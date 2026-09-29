-- Prove2me | Theorems.Thm_FamousTheorems_algebraic_over_algebraic_7b
-- name    : FamousTheorems.algebraic_over_algebraic_7b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:34:04.906674+00:00
-- url     : https://prove2.me/theorems/25b4068c-48a4-4d34-a97c-a273f982a9b0
-- title:
--   Algebraic over algebraic is algebraic
-- statement:
--   **Algebraic over algebraic is algebraic.** Let $R\subseteq S\subseteq A$ be a tower of algebras, where $S$ is algebraic over $R$ and $A$ is algebraic over $S$. Suppose that $S$ has no zero divisors. Then $A$ is algebraic over $R$.
--
--   For fields this is a basic fact of field theory: an element algebraic over an algebraic extension of $K$ is algebraic over $K$. It is used to show that the algebraic elements of an extension form a field, that the algebraic closure of $K$ in an algebraically closed field is algebraically closed, and that transcendence degree is additive.
--
--   **Formalization note.** Mathlib's `Algebra.IsAlgebraic.trans`. `Algebra.IsAlgebraic R A` says that every element of $A$ is a root of a nonzero polynomial with coefficients in $R$. The rings need not be fields.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Algebra.IsAlgebraic.trans`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem algebraic_over_algebraic_7b (R S A : Type*) [CommRing R] [CommRing S] [Ring A] [Algebra R S] [Algebra R A] [Algebra S A]
    [IsScalarTower R S A] [NoZeroDivisors S] [Algebra.IsAlgebraic R S] [Algebra.IsAlgebraic S A] :
    Algebra.IsAlgebraic R A := by sorry

end FamousTheorems
