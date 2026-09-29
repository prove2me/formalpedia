-- Prove2me | Theorems.Thm_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem
-- name    : Finsupp.card_le_macaulayPow_card_of_forall_sub_single_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/24282314-0dfc-50ac-8168-90001c1a57f0
-- title:
--   Macaulay's bound for monomial sets one degree up
-- statement:
--   Fix natural numbers $n$ and $d$ with $1 \le d$. Monomials in $x_0,\dots,x_n$ are encoded as finitely supported functions $\mathrm{Fin}(n+1) \to \mathbb{N}$, with `Finsupp.degree` the sum of the exponents. Let $B$ be a finite set of such exponent vectors, all of degree $d$, and let $C$ be a finite set of exponent vectors, all of degree $d+1$, subject to the divisibility hypothesis: for every $u \in C$ and every index $i$ with $u\,i \ge 1$, the vector $u - \mathrm{single}\,i\,1$ (that is, $u$ with the $i$-th exponent decreased by one, the monomial $u/x_i$) belongs to $B$. The conclusion is $\#C \le$ [`Nat.macaulayPow d`](def/Nat_MacaulayPow.html#L7) $(\#B)$, where [`Nat.macaulayPow`](def/Nat_MacaulayPow.html#L7) is defined by recursion on its first argument: `macaulayPow 0 a = 0`, and for $d \ge 0$, `macaulayPow (d+1) a` $= \binom{k+1}{d+2} +$ `macaulayPow d` $\bigl(a - \binom{k}{d+1}\bigr)$, where $k$ is the largest natural number $\le a + d + 1$ with $\binom{k}{d+1} \le a$. Thus $\#C$ is bounded by Macaulay's upper pseudo-power $(\#B)^{\langle d \rangle}$.
--
--   This is the purely combinatorial core of Macaulay's theorem on Hilbert functions: the set of degree-$(d+1)$ monomials whose degree-$d$ divisors all lie in a given family $B$ cannot exceed the Macaulay pseudo-power of $\#B$. It is used to prove [`MvPolynomial.finrank_piece_succ_le_macaulayPow`](thm.html#MvPolynomial.finrank_piece_succ_le_macaulayPow), the corresponding bound on the dimensions of consecutive graded pieces of a quotient of a polynomial ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.lean

import Mathlib
import Definitions.Def_Nat_MacaulayPow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Finsupp.card_le_macaulayPow_card_of_forall_sub_single_mem
    (n d : ℕ) (hd : 1 ≤ d) (B : Finset (Fin (n + 1) →₀ ℕ)) (hB : ∀ m ∈ B, m.degree = d)
    (C : Finset (Fin (n + 1) →₀ ℕ)) (hC : ∀ u ∈ C, u.degree = d + 1)
    (hCB : ∀ u ∈ C, ∀ i : Fin (n + 1), 1 ≤ u i → u - Finsupp.single i 1 ∈ B) :
    C.card ≤ Nat.macaulayPow d B.card := by sorry
