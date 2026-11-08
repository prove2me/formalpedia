-- Prove2me | Theorems.Thm_BKAbsorption_cyclic_term_prime
-- name    : BKAbsorption.cyclic_term_prime
-- status  : Open
-- author  : @Alien60
-- created : 2026-11-07T14:13:41.260211+00:00
-- url     : https://prove2.me/theorems/16f82556-cd29-4422-ae46-61d0386475f8
-- title:
--   Cyclic terms of prime arity
-- statement:
--   $L$ is a signature without relation symbols. A finite algebra $A$ lies in a Taylor variety: it is idempotent ($f(a,\dots,a)=a$ for every basic operation) and satisfies the identities of a fixed Taylor term $t$ of arity $k$: for each $j<k$, $t(\square_0,\dots,\square_{k-1})\approx t(\triangle_0,\dots,\triangle_{k-1})$ with $\square_i,\triangle_i\in\{x,y\}$, $\square_j=x$, $\triangle_j=y$. Let $p$ be a prime with $p>|A|$. Then $A$ has a $p$-ary cyclic term operation: an idempotent term operation $t$ with $t(x_0,x_1,\dots,x_{p-1})=t(x_1,\dots,x_{p-1},x_0)$ for all $x_i\in A$.
-- source:
--   L. Barto, M. Kozik, Absorbing subalgebras, cyclic terms, and the constraint satisfaction problem, Logical Methods in Computer Science 8(1:07) 2012, https://doi.org/10.2168/LMCS-8(1:7)2012 (arXiv:1201.0557), Thm 4.2

import Definitions.Def_BKAbsorption_defs

universe u v w w'

open FirstOrder FirstOrder.Language

namespace BKAbsorption

variable {L : FirstOrder.Language.{u, v}} [L.IsAlgebraic]

/-- Barto–Kozik, Theorem 4.2.  Let `A` be a finite algebra in a Taylor variety (`A` satisfies the
idempotency and Taylor identities of a Taylor datum `T`) and let `p` be a prime with
`p > |A|`.  Then `A` has a `p`-ary cyclic term operation. -/
theorem cyclic_term_prime {A : Type w} [L.Structure A] [Finite A] (T : TaylorDatum L)
    (hA : IsTaylorAlg T A) (p : ℕ) (hp : p.Prime) (hpA : Nat.card A < p) :
    HasCyclicTermOp L A p := by sorry

end BKAbsorption
