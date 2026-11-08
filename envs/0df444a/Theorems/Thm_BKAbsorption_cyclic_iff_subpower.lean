-- Prove2me | Theorems.Thm_BKAbsorption_cyclic_iff_subpower
-- name    : BKAbsorption.cyclic_iff_subpower
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-07T14:13:29.390059+00:00
-- url     : https://prove2.me/theorems/664824f2-3c59-45c2-8a18-237d26092488
-- title:
--   Cyclic terms via cyclic relations
-- statement:
--   $L$ is a signature without relation symbols and $A$ a finite idempotent algebra ($f(a,\dots,a)=a$ for every basic operation); $k\ge2$. $A$ has a $k$-ary cyclic term operation (an idempotent term operation with $t(x_0,x_1,\dots,x_{k-1})=t(x_1,\dots,x_{k-1},x_0)$) iff every nonempty cyclic subuniverse $R$ of $A^k$ (closed under $(a_0,\dots,a_{k-1})\mapsto(a_1,\dots,a_{k-1},a_0)$) contains a constant tuple $(a,\dots,a)$.
-- source:
--   L. Barto, M. Kozik, Absorbing subalgebras, cyclic terms, and the constraint satisfaction problem, Logical Methods in Computer Science 8(1:07) 2012, https://doi.org/10.2168/LMCS-8(1:7)2012 (arXiv:1201.0557), Lemma 4.4

import Definitions.Def_BKAbsorption_defs

universe u v w w'

open FirstOrder FirstOrder.Language

namespace BKAbsorption

variable {L : FirstOrder.Language.{u, v}} [L.IsAlgebraic]

/-- Barto–Kozik, Lemma 4.4 (from Barto–Kozik–Maróti–Niven).  For a finite idempotent algebra `A`
and `k ≥ 2` the following are equivalent: `A` has a `k`-ary cyclic term operation; every
nonempty cyclic subuniverse of `A^k` contains a constant tuple. -/
theorem cyclic_iff_subpower {A : Type w} [L.Structure A] [Finite A] (hid : IsIdempotent L A)
    (k : ℕ) (hk : 2 ≤ k) :
    HasCyclicTermOp L A k ↔
      ∀ R : Set (Fin k → A), R.Nonempty → IsSubpower L R → IsCyclicRel R →
        ∃ a : A, (fun _ => a) ∈ R := by sorry

end BKAbsorption
