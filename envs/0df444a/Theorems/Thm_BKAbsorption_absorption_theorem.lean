-- Prove2me | Theorems.Thm_BKAbsorption_absorption_theorem
-- name    : BKAbsorption.absorption_theorem
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-07T14:12:48.668699+00:00
-- url     : https://prove2.me/theorems/8a3d0e05-ad01-4d34-a939-0bdf2bf2c325
-- title:
--   Absorption Theorem
-- statement:
--   $L$ is a signature without relation symbols. $A$ and $B$ are finite algebras in one Taylor variety: both are idempotent and satisfy the identities of one fixed Taylor term. $B\trianglelefteq A$ ($B$ absorbs $A$): $B$ is a subuniverse and some term operation $t$ gives $t(a_0,\dots,a_{n-1})\in B$ whenever all $a_i$ but at most one lie in $B$; proper means $\emptyset\neq B\neq A$; $B\trianglelefteq\!\!\trianglelefteq A$: $B$ is nonempty, absorbs $A$, and no proper subalgebra of $B$ absorbs $A$. $R\le_S A\times B$: $R$ is a subuniverse of $A\times B$ (coordinatewise operations) with both projections onto. $R$ is linked: any two elements of its first projection are joined by a chain whose consecutive elements have a common $R$-neighbour. If $R\le_S A\times B$ is linked and $R\neq A\times B$, then $A$ or $B$ has a proper absorbing subuniverse.
-- source:
--   L. Barto, M. Kozik, Absorbing subalgebras, cyclic terms, and the constraint satisfaction problem, Logical Methods in Computer Science 8(1:07) 2012, https://doi.org/10.2168/LMCS-8(1:7)2012 (arXiv:1201.0557), Thm 2.11

import Definitions.Def_BKAbsorption_defs

universe u v w w'

open FirstOrder FirstOrder.Language

namespace BKAbsorption

variable {L : FirstOrder.Language.{u, v}} [L.IsAlgebraic]

/-- Barto–Kozik, Theorem 2.11 (the Absorption Theorem).  Let `A, B` be finite algebras in a
Taylor variety (both satisfy the identities of one Taylor datum `T`) and let `R` be a proper,
subdirect and linked subalgebra of `A × B`.  Then `A` or `B` has a proper absorbing
subalgebra. -/
theorem absorption_theorem {A : Type w} {B : Type w'} [L.Structure A] [L.Structure B]
    [Finite A] [Finite B] (T : TaylorDatum L) (hA : IsTaylorAlg T A) (hB : IsTaylorAlg T B)
    (R : L.Substructure (A × B)) (hsd : Subdirect (R : Set (A × B)))
    (hlk : Linked (R : Set (A × B))) (hpr : (R : Set (A × B)) ≠ Set.univ) :
    HasProperAbsorbing L A ∨ HasProperAbsorbing L B := by sorry

end BKAbsorption
