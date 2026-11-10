-- Prove2me | Theorems.Thm_BKAbsorption_cyclic_of_congruence
-- name    : BKAbsorption.cyclic_of_congruence
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-09T16:14:44.840887+00:00
-- url     : https://prove2.me/theorems/cd95fdf1-0fc1-4732-bea4-1d338409f7d0
-- title:
--   Barto–Kozik Claim 4.5: cyclic terms lift through a congruence
-- statement:
--   Let $A$ be a finite idempotent algebra, $k\ge 2$, and $	heta$ a congruence of $A$. Suppose that
--
--   1. some $k$-ary term $t$ is cyclic modulo $	heta$, i.e. $t(x_0,\dots,x_{k-1})\mathrel{	heta} t(x_1,\dots,x_{k-1},x_0)$ for all $x\in A^k$ (equivalently, $A/	heta$ has a $k$-ary cyclic term operation), and
--   2. every $	heta$-block, as a subalgebra of $A$, has a $k$-ary cyclic term operation.
--
--   Then $A$ has a $k$-ary cyclic term operation.
--
--   This is the reduction in Claim 4.5 of the paper (also in Barto–Kozik–Maróti–McKenzie–Niven 2009): a minimal counterexample to Theorem 4.2 must be simple. The proof uses Lemma 4.4 (cyclic terms ⇔ every nonempty cyclic subpower contains a constant tuple).
--
--   *Formalization note.* The congruence is an equivalence relation `r` compatible with all basic operations; a block is given as a substructure whose carrier is an `r`-class.
-- source:
--   Barto–Kozik, Absorbing subalgebras, cyclic terms and the constraint satisfaction problem, LMCS 8(1:07) 2012, arXiv:1201.0557, Section 4, Claim 4.5 (p. 21) and Lemma 4.4 (p. 20).

import Definitions.Def_BKAbsorption_defs

universe u v w w'

open FirstOrder FirstOrder.Language

namespace BKAbsorption

variable {L : FirstOrder.Language.{u, v}} [L.IsAlgebraic]

/-- Barto–Kozik, Claim 4.5 (general form; cf. [BKM+09]).  Let `A` be a finite idempotent algebra
and `r` a congruence of `A`.  If some `k`-ary term operation is cyclic modulo `r` (i.e. `A/r` has a
`k`-ary cyclic term operation) and every `r`-block, viewed as a subalgebra of `A`, has a `k`-ary
cyclic term operation, then `A` has a `k`-ary cyclic term operation. -/
theorem cyclic_of_congruence {A : Type w} [L.Structure A] [Finite A] (hid : IsIdempotent L A)
    (k : ℕ) (hk : 2 ≤ k) (r : A → A → Prop) (hr : Equivalence r)
    (hcomp : ∀ (n : ℕ) (f : L.Functions n) (x y : Fin n → A), (∀ i, r (x i) (y i)) →
      r (Structure.funMap f x) (Structure.funMap f y))
    (hquot : ∃ t : L.Term (Fin k), ∀ x : Fin k → A,
      r (t.realize x) (t.realize (x ∘ finRotate k)))
    (hblock : ∀ C : L.Substructure A, (∃ a, (C : Set A) = {x | r x a}) →
      HasCyclicTermOp L C k) :
    HasCyclicTermOp L A k := by sorry

end BKAbsorption
