-- Prove2me | Theorems.Thm_BKAbsorption_cyclic_simple_core
-- name    : BKAbsorption.cyclic_simple_core
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-09T16:14:40.669499+00:00
-- url     : https://prove2.me/theorems/3f0a06ee-b617-474b-8e4c-cb4838a178a7
-- title:
--   Barto–Kozik Thm 4.2, simple case (Claims 4.6–4.14)
-- statement:
--   Let $A$ be a finite algebra in a Taylor variety (given by a Taylor datum $T$) and let $p>|A|$ be a prime. Assume
--
--   1. $A$ is simple: every congruence of $A$ is the identity or the full relation, and
--   2. every proper subalgebra of $A$ has a $p$-ary cyclic term operation.
--
--   Then $A$ has a $p$-ary cyclic term operation.
--
--   This is the core of the proof of Theorem 4.2 for a minimal counterexample: a cyclic subdirect subpower $R\le A^p$ without constant tuples is ruled out by proving properties (P1) and (P2) by induction on $n$ (Claims 4.6–4.12) and applying the Loop Lemma (Theorem 3.6) to the digraph on $R_n$ (Claims 4.13–4.14).
--
--   *Formalization note.* A congruence is an equivalence relation `r` compatible with all basic operations; proper subalgebras are substructures with carrier different from $A$.
-- source:
--   Barto–Kozik, Absorbing subalgebras, cyclic terms and the constraint satisfaction problem, LMCS 8(1:07) 2012, arXiv:1201.0557, Section 4, proof of Theorem 4.2, Claims 4.6–4.14 (p. 21–24).

import Definitions.Def_BKAbsorption_defs

universe u v w w'

open FirstOrder FirstOrder.Language

namespace BKAbsorption

variable {L : FirstOrder.Language.{u, v}} [L.IsAlgebraic]

/-- Barto–Kozik, proof of Theorem 4.2 for a minimal counterexample (Claims 4.6–4.14, using the
Loop Lemma 3.6).  Let `A` be a finite algebra in the Taylor variety of `T` and `p > |A|` a prime.
Assume `A` is simple (every congruence is trivial or full) and every proper subalgebra of `A` has
a `p`-ary cyclic term operation.  Then `A` has a `p`-ary cyclic term operation. -/
theorem cyclic_simple_core {A : Type w} [L.Structure A] [Finite A] (T : TaylorDatum L)
    (hA : IsTaylorAlg T A) (p : ℕ) (hp : p.Prime) (hpA : Nat.card A < p)
    (hsimple : ∀ r : A → A → Prop, Equivalence r →
      (∀ (n : ℕ) (f : L.Functions n) (x y : Fin n → A), (∀ i, r (x i) (y i)) →
        r (Structure.funMap f x) (Structure.funMap f y)) →
      (∀ a b, r a b → a = b) ∨ ∀ a b, r a b)
    (hsub : ∀ S : L.Substructure A, (S : Set A) ≠ Set.univ → HasCyclicTermOp L S p) :
    HasCyclicTermOp L A p := by sorry

end BKAbsorption
