-- Prove2me | Theorems.Thm_BKAbsorption_loop_nonabsorbing_step
-- name    : BKAbsorption.loop_nonabsorbing_step
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-09T16:07:36.000424+00:00
-- url     : https://prove2.me/theorems/2b3ed495-f218-4009-96b9-601ef4b4b29d
-- title:
--   Barto–Kozik Claim 3.11: non-absorbing case of the Loop Lemma
-- statement:
--   Throughout, $A$ is a finite algebra, $E\le A^2$ is a subuniverse (a digraph on $A$ compatible with the operations), and $S\subseteq A$ is a subuniverse such that the induced digraph $G|_S=(S,E\cap S^2)$ is *smooth* (every vertex of $S$ has an in- and an out-neighbour in $S$). A walk of *algebraic length* $z$ counts forward edges minus backward edges. Absorption is relative: $X$ absorbs $S$ if $X$ is a subuniverse and some term $t$ of positive arity satisfies $t(x_0,\dots,x_{n-1})\in X$ whenever all $x_i\in S$ and all but at most one $x_i\in X$.
--
--   Assume $A$ lies in the Taylor variety given by a Taylor datum $T$. Suppose $G|_S$ is weakly connected and of algebraic length $1$ (witnessed by $a\in S$), and no nonempty subuniverse $C\subsetneq S$ absorbs $S$. Then either $E$ has a loop at some vertex of $S$, or there is a nonempty subuniverse $B\subsetneq S$ such that $G|_B$ is smooth and of algebraic length $1$.
--
--   This is the second case of the paper's proof of Theorem 3.6: for the least $k$ with $\{a\}F[k,m]=S$, Theorem 2.3 gives $E^k\cap S^2=S^2$; then $B$ is the smooth part of $\{a\}F[k-1,m]$ (Claim 3.11), and $k=1$ gives a loop.
-- source:
--   Barto–Kozik, Absorbing subalgebras, cyclic terms and the constraint satisfaction problem, LMCS 8(1:07) 2012, arXiv:1201.0557, Section 3.3, Theorem 2.3 and Claim 3.11 (p. 18–19).

import Definitions.Def_BKAbsorption_defs

universe u v w w'

open FirstOrder FirstOrder.Language

namespace BKAbsorption

variable {L : FirstOrder.Language.{u, v}} [L.IsAlgebraic]

/-- Barto–Kozik, Claim 3.11 (non-absorbing case of the Loop Lemma, relative form).  Let `A` be a
finite algebra in the Taylor variety of `T`, `E ≤ A²` a subuniverse, and `S` a subuniverse of `A`
such that `(S, E ∩ S²)` is smooth, weakly connected and of algebraic length `1`, and such that
no nonempty proper subuniverse of `S` absorbs `S` (relative absorption).  Then either
`E` has a loop in `S`, or there is a nonempty subuniverse `B ⊊ S` such that `(B, E ∩ B²)` is
smooth and of algebraic length `1`. -/
theorem loop_nonabsorbing_step {A : Type w} [L.Structure A] [Finite A] (T : TaylorDatum L)
    (hA : IsTaylorAlg T A) (E : L.Substructure (A × A)) (S : Set A) (hS : IsSubuniverse L S)
    (hsm : ∀ x ∈ S, (∃ y ∈ S, (x, y) ∈ E) ∧ ∃ y ∈ S, (y, x) ∈ E)
    (a : A) (ha : a ∈ S) (hlen : Walk ((E : Set (A × A)) ∩ S ×ˢ S) a a 1)
    (hconn : ∀ x ∈ S, ∃ z, Walk ((E : Set (A × A)) ∩ S ×ˢ S) a x z)
    (hnoabs : ∀ C : Set A, C ⊆ S → C.Nonempty →
      (IsSubuniverse L C ∧ ∃ (n : ℕ) (t : L.Term (Fin n)), 0 < n ∧
        ∀ (k : Fin n) (x : Fin n → A), (∀ i, x i ∈ S) → (∀ i, i ≠ k → x i ∈ C) →
          t.realize x ∈ C) → C = S) :
    (∃ x ∈ S, (x, x) ∈ E) ∨
      ∃ B : Set A, B ⊂ S ∧ B.Nonempty ∧ IsSubuniverse L B ∧
        (∀ x ∈ B, (∃ y ∈ B, (x, y) ∈ E) ∧ ∃ y ∈ B, (y, x) ∈ E) ∧
        ∃ b ∈ B, Walk ((E : Set (A × A)) ∩ B ×ˢ B) b b 1 := by sorry

end BKAbsorption
