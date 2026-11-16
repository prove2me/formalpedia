-- Prove2me | Theorems.Thm_CatalyticSorting494_Sorting_Supplement_theorem_4_3
-- name    : CatalyticSorting494.Sorting.Supplement.theorem_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:19:28.150455+00:00
-- url     : https://prove2.me/theorems/eba69227-73c7-4142-839b-b0d58eb196d2
-- title:
--   Theorem 4.3 — catalytic evaluation of low-multiplicative-depth $\#\mathrm{NC}(K_n)$ circuits in time $\tilde O(w3^dT)$
-- statement:
--   Let $K=(K_n)$ be an $(S,T)$-uniform family of finite rings, not necessarily commutative (Definition 4.2), with a fixed witness of uniformity, and write $L_n=\lceil\log_2|K_n|\rceil$. Then there is a single catalytic algorithm in the dirty-XOR-output model which, given $n$, an $\#\mathrm{NC}(K_n)$ circuit $C$ with $w$ wires and multiplicative depth $d$ (Definition 4.1), and values of all its input wires, computes the values of all of $C$'s output wires, using
--
--   $$\text{time } \tilde O\!\left(w\,3^{d}\,T(n)\right),\qquad \text{clean space } O\big(\log w+d+\log T(n)+S(n)\big),\qquad \text{catalytic space } \tilde O\!\left(w\log|K_n|\right).$$
--
--   Precisely: there are one machine $M$, one capacity function $c(w,d,n)$ and constants $A,k$, depending only on the ring family and its uniformity witness, such that for every $n$, every well-formed circuit $C$ over $K_n$ and every input assignment, the capacity $c(w,d,n)$ is at most $A N (\log_2(N+2))^k$ with $N=(w+1)(L_n+1)$, and for every initial catalytic content $z$ of that length, $M$ halts within $A N'(\log_2(N'+2))^k$ steps, $N'=(w+1)\,3^d\,(T(n)+1)$, charged at most $A(\log_2(w+2)+d+\log_2(T(n)+2)+S(n))$ clean bits, having XORed the codes $e_n$ of the output values into the beginning of the catalytic tape and restored every other catalytic bit.
--
--   The factor is $3^d$, not the $2^d$ of the Boolean Theorem 1.1, and only the layers containing fan-in 2 product gates count towards $d$. The circuit is arbitrary (not succinctly uniform) and is part of the input, constants included. This is a companion theorem of the mission; it is not used in the proof of the sorting corollary. Through Corollary 4.11 it yields Theorem 1.4.
--
--   **Formalization Note** The ring operations are available only through the uniformity witness's machines, which the algorithm must simulate at their charged cost. $\log$ is $\lfloor\log_2\rfloor$ of shifted arguments.
--
--   Differences from the source:
--   - encoding: a ring K_n → a finite ring with 1 (Ring, Fintype), commutativity not assumed; reason: Definition 4.2 forces finiteness (codes of length ⌈log|K_n|⌉) and a unit (e(1)); no instance of the source is excluded
--   - generalization: fan-in 1 “×x” gates → both right multiplication u ↦ u·x and left multiplication u ↦ x·u by every constant; reason: for a noncommutative ring the side of “×x” is not specified, and a gateset containing both covers either reading; on commutative rings both are the source's “×x”
--   - encoding: Õ(w3^d T) time, Õ(w log|K_n|) dirty space → softBound A k ((w+1)·3^d·(T(n)+1)) and softBound A k ((w+1)·(⌈log₂|K_n|⌉+1)), i.e. A·N·(log₂(N+2))^k; reason: the shifts by 1 only cover w = 0, T(n) = 0 or |K_n| ≤ 2 and change the bounds by at most a constant factor otherwise
--   - encoding: clean space O(log w + d + log T + S) → A·(⌊log₂(w+2)⌋ + d + ⌊log₂(T(n)+2)⌋ + S(n)); reason: shifted logarithms are harmless for w, T(n) ∈ {0,1}
--   - encoding: a #NC(K_n) circuit and a setting of its input wires as input; the index n implicit → the input tape holds 1^n, then the circuit and the codes e_n of its input values and constants (ArithCircuit.encode); the output is the codes e_n of all output values XORed into the catalytic prefix; reason: the algorithm must know n to run the uniformity machines, which take 1^n first; Definition 2.2's dirty-XOR output
--   - encoding: w wires → wireCount: incoming wires plus one per input, gate and output; reason: the base mission's convention; within a constant factor of the number of incoming wires for circuits without unused nodes
-- source:
--   Adelmo Morrison Orozco, Nathan S. Sheffield, Ryan Williams, STOC 2027 submission #494 (October 2026), Theorem 4.3, printed p.14 (PDF p.15); Definitions 4.1 and 4.2, printed p.14 (PDF p.15); dirty-XOR-output model Definition 2.2, printed p.8 (PDF p.9)

import Mathlib
import Definitions.Def_CatalyticSorting494_Sorting_Machine
import Definitions.Def_CatalyticSorting494_Sorting_SymCircuit
import Definitions.Def_CatalyticSorting494_Sorting_Supplement_ArithCircuit
import Definitions.Def_CatalyticSorting494_Sorting_Supplement_UniformRing

open CatalyticSorting494.Sorting

namespace CatalyticSorting494.Sorting.Supplement

/-- Theorem 4.3. For an `(S, T)`-uniform ring family `K` with witness `W`, one machine `M`, one
catalytic capacity function `c` of the size, multiplicative depth and index, and one pair of
constants `A, k` work for all `n`, all well-formed `#NC(K_n)` circuits, all input assignments and all
initial catalytic contents. The factors `w + 1` and `T n + 1` cover the degenerate values `0`. -/
theorem theorem_4_3 (K : ℕ → Type*) [∀ n, Ring (K n)] [∀ n, Fintype (K n)]
    (S T : ℕ → ℕ) (W : UniformRing K S T) :
    ∃ (M : Machine) (c : ℕ → ℕ → ℕ → ℕ) (A k : ℕ),
      ∀ (n : ℕ) (C : ArithCircuit (K n)) (x : List (K n)),
        C.WellFormed → x.length = C.numInputs →
        c C.wireCount C.multDepth n ≤ softBound A k ((C.wireCount + 1) * (ringWidth K n + 1)) ∧
        ∀ z : List Bool, z.length = c C.wireCount C.multDepth n →
          ComputesWithin M (C.encode (W.code n) n x) z ((C.eval x).flatMap (W.code n))
            (softBound A k ((C.wireCount + 1) * 3 ^ C.multDepth * (T n + 1)) : ℕ)
            (A * (Nat.log 2 (C.wireCount + 2) + C.multDepth + Nat.log 2 (T n + 2) + S n)) := by sorry

end CatalyticSorting494.Sorting.Supplement
