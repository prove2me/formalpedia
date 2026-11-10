-- Prove2me | Theorems.Thm_BKAbsorption_loop_absorbing_step
-- name    : BKAbsorption.loop_absorbing_step
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-09T16:07:34.777574+00:00
-- url     : https://prove2.me/theorems/12a25e5f-f5a1-4f74-a7e9-403c865e0d4c
-- title:
--   Barto–Kozik Lemma 3.3 + Claims 3.9–3.10: absorbing case of the Loop Lemma
-- statement:
--   Throughout, $A$ is a finite algebra, $E\le A^2$ is a subuniverse (a digraph on $A$ compatible with the operations), and $S\subseteq A$ is a subuniverse such that the induced digraph $G|_S=(S,E\cap S^2)$ is *smooth* (every vertex of $S$ has an in- and an out-neighbour in $S$). A walk of *algebraic length* $z$ counts forward edges minus backward edges. Absorption is relative: $X$ absorbs $S$ if $X$ is a subuniverse and some term $t$ of positive arity satisfies $t(x_0,\dots,x_{n-1})\in X$ whenever all $x_i\in S$ and all but at most one $x_i\in X$.
--
--   Assume $A$ is idempotent. Let $a\in S$ lie on a closed walk of algebraic length $1$ in $G|_S$, and let $I
--   eq S$ be a nonempty set contained in the weak component of $a$ in $G|_S$ which absorbs $S$. Then there is a nonempty subuniverse $S'\subsetneq S$ that absorbs $S$ such that $G|_{S'}$ is smooth, weakly connected and of algebraic length $1$ (some $b\in S'$ lies on a closed walk of algebraic length $1$ in $G|_{S'}$ and reaches every vertex of $S'$).
--
--   This is the first case of the paper's proof of Theorem 3.6: $S'$ is the smooth part of $IP$ for the longest initial segment $P$ of a fence with $IP
--   e H$ (Claim 3.9, Lemma 2.5, Proposition 3.2, Lemma 3.3), and Claim 3.10 shows it is connected of algebraic length 1.
-- source:
--   Barto–Kozik, Absorbing subalgebras, cyclic terms and the constraint satisfaction problem, LMCS 8(1:07) 2012, arXiv:1201.0557, Section 3.3, Lemma 3.3 (p. 16), Claims 3.9–3.10 (p. 17–18).

import Definitions.Def_BKAbsorption_defs

universe u v w w'

open FirstOrder FirstOrder.Language

namespace BKAbsorption

variable {L : FirstOrder.Language.{u, v}} [L.IsAlgebraic]

/-- Barto–Kozik, Lemma 3.3 + Claims 3.9–3.10 (absorbing case of the Loop Lemma, relative form).
Let `A` be a finite idempotent algebra, `E ≤ A²` a subuniverse, and `S` a subuniverse of `A`
with `(S, E ∩ S²)` smooth.  Let `a ∈ S` lie on a closed walk of algebraic length `1` in
`(S, E ∩ S²)`, and let `I ≠ S` be a nonempty subuniverse contained in the weak component of `a`
which absorbs `S` (relative absorption: some term `t` of positive arity sends every `S`-tuple with
all but at most one entry in `I` into `I`).  Then there is a nonempty subuniverse `S' ⊊ S`
absorbing `S` such that `(S', E ∩ S'²)` is smooth, weakly connected and of algebraic length `1`. -/
theorem loop_absorbing_step {A : Type w} [L.Structure A] [Finite A] (hid : IsIdempotent L A)
    (E : L.Substructure (A × A)) (S : Set A) (hS : IsSubuniverse L S)
    (hsm : ∀ x ∈ S, (∃ y ∈ S, (x, y) ∈ E) ∧ ∃ y ∈ S, (y, x) ∈ E)
    (a : A) (ha : a ∈ S) (hlen : Walk ((E : Set (A × A)) ∩ S ×ˢ S) a a 1)
    (I : Set A) (hIne : I.Nonempty) (hIS : I ≠ S)
    (hIc : ∀ x ∈ I, ∃ z, Walk ((E : Set (A × A)) ∩ S ×ˢ S) a x z)
    (hIabs : IsSubuniverse L I ∧ ∃ (n : ℕ) (t : L.Term (Fin n)), 0 < n ∧
      ∀ (k : Fin n) (x : Fin n → A), (∀ i, x i ∈ S) → (∀ i, i ≠ k → x i ∈ I) →
        t.realize x ∈ I) :
    ∃ S' : Set A, S' ⊂ S ∧ S'.Nonempty ∧
      (IsSubuniverse L S' ∧ ∃ (n : ℕ) (t : L.Term (Fin n)), 0 < n ∧
        ∀ (k : Fin n) (x : Fin n → A), (∀ i, x i ∈ S) → (∀ i, i ≠ k → x i ∈ S') →
          t.realize x ∈ S') ∧
      (∀ x ∈ S', (∃ y ∈ S', (x, y) ∈ E) ∧ ∃ y ∈ S', (y, x) ∈ E) ∧
      ∃ b ∈ S', Walk ((E : Set (A × A)) ∩ S' ×ˢ S') b b 1 ∧
        ∀ x ∈ S', ∃ z, Walk ((E : Set (A × A)) ∩ S' ×ˢ S') b x z := by sorry

end BKAbsorption
