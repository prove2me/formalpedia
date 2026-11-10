-- Prove2me | Theorems.Thm_BKAbsorption_component_subuniverse
-- name    : BKAbsorption.component_subuniverse
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-09T16:07:34.547712+00:00
-- url     : https://prove2.me/theorems/5e47d20e-e871-4637-a4c7-ac1878385c58
-- title:
--   Barto–Kozik Claim 3.8: weak components of algebraic length 1 are subuniverses
-- statement:
--   Throughout, $A$ is a finite algebra, $E\le A^2$ is a subuniverse (a digraph on $A$ compatible with the operations), and $S\subseteq A$ is a subuniverse such that the induced digraph $G|_S=(S,E\cap S^2)$ is *smooth* (every vertex of $S$ has an in- and an out-neighbour in $S$). A walk of *algebraic length* $z$ counts forward edges minus backward edges. Absorption is relative: $X$ absorbs $S$ if $X$ is a subuniverse and some term $t$ of positive arity satisfies $t(x_0,\dots,x_{n-1})\in X$ whenever all $x_i\in S$ and all but at most one $x_i\in X$.
--
--   Assume $A$ is idempotent. If $a\in S$ lies on a closed walk of algebraic length $1$ in $G|_S$, then the weak component $\{x : a \text{ is connected to } x \text{ by a walk in } G|_S\}$ is a subuniverse of $A$.
--
--   (In the paper this follows from Claim 3.8: every vertex of the component is reached from $a$ by one common fence, and applying an operation coordinatewise along the fence preserves the component, by idempotency.)
-- source:
--   Barto–Kozik, Absorbing subalgebras, cyclic terms and the constraint satisfaction problem, LMCS 8(1:07) 2012, arXiv:1201.0557, Section 3.3, Claim 3.8 and its use in the proof of Theorem 3.6 (p. 17–18).

import Definitions.Def_BKAbsorption_defs

universe u v w w'

open FirstOrder FirstOrder.Language

namespace BKAbsorption

variable {L : FirstOrder.Language.{u, v}} [L.IsAlgebraic]

/-- Barto–Kozik, consequence of Claim 3.8 (relative form).  Let `A` be a finite idempotent
algebra, `E ≤ A²` a subuniverse, and `S` a subuniverse of `A` such that the induced digraph
`(S, E ∩ S²)` is smooth.  If `a ∈ S` lies on a closed walk of algebraic length `1` in `(S, E ∩ S²)`,
then the weak component of `a` in `(S, E ∩ S²)` is a subuniverse of `A`. -/
theorem component_subuniverse {A : Type w} [L.Structure A] [Finite A] (hid : IsIdempotent L A)
    (E : L.Substructure (A × A)) (S : Set A) (hS : IsSubuniverse L S)
    (hsm : ∀ x ∈ S, (∃ y ∈ S, (x, y) ∈ E) ∧ ∃ y ∈ S, (y, x) ∈ E)
    (a : A) (ha : a ∈ S) (hlen : Walk ((E : Set (A × A)) ∩ S ×ˢ S) a a 1) :
    IsSubuniverse L {x | ∃ z, Walk ((E : Set (A × A)) ∩ S ×ˢ S) a x z} := by sorry

end BKAbsorption
