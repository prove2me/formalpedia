-- Prove2me | Theorems.Thm_AESIndependence_Main_circuit_expanders
-- name    : AESIndependence.Main.circuit_expanders
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T04:12:45.114358+00:00
-- url     : https://prove2.me/theorems/b4403283-79de-4fb0-b412-5f814c8c5e02
-- title:
--   Theorem 2.19 — alternating-group expanders with linear-size reversible circuits
-- statement:
--   There exist absolute witnesses $\gamma>0$, $a>0$ and an integer $c\ge1$ with the following property simultaneously for every binary dimension $n\ge2$. There are $c$ distinct even permutations $g_i$ of $\mathbb F_2^n$ such that the lazy Cayley walk on the alternating group satisfies
--   $$K=\frac12 I+\frac1{4c}\sum_{i=1}^c(g_i+g_i^{-1}),\qquad \operatorname{gap}(K)\ge\gamma.$$
--   Each $g_i$ and each inverse has a circuit of at most $an$ NOT, CNOT and Toffoli gates on those same $n$ wires, with no ancillary bits. Equality is required for every assignment. The universal witnesses precede the arbitrary dimension; they are produced by the theorem rather than assumed per cipher. This supplies the source's general binary-dimension circuit expander, including every AES dimension $n=bd^2$ with $b\ge4,d\ge2$.
--
--   **Formalization Note** Wires are indexed by `Fin n`. The condition $n\ge2$ excludes precisely the zero- and one-wire alternating groups, both of which have just one element and hence no second eigenvalue.
--
--   Differences from the source:
--   - encoding: n-bit strings and the second eigenvalue of the alternating-group walk → binary assignments on Fin n, for every natural n ≥ 2; reason: Fin n indexes all n wires without an AES factorization restriction. For n = 0 or 1 the alternating group is a singleton and the source second eigenvalue is undefined; every dimension with a defined second eigenvalue is retained.
--   - encoding: absolute γ,c and O(n) circuits; constant spectral gap γ → ∃ γ a c with γ>0,a>0,c≥1 before every n; an injective generator list, gap at least γ, and both circuit lengths at most a n; reason: γ is a uniform positive lower bound, as used in Proposition 2.21; no unsupported numeral or instance-dependent witness is supplied.
--   - encoding: lazy walk on the alternating group and ancilla-free circuits → left Cayley multiplication and lists of gates on exactly the assignment wire type; reason: The group state space, both inverse generators, laziness 1/2 and weights 1/(4c) are retained.
-- source:
--   Angelos Pelecanos, Stefano Tessaro, Vinod Vaikuntanathan, STOC 2027 submission #1279 (October 2026), Theorem 2.19, p.14 (PDF p.14)

import Mathlib
import Definitions.Def_AESIndependence_Main_ReferenceChain

namespace AESIndependence.Main
open scoped BigOperators Classical

theorem circuit_expanders :
    ∃ (γ a : ℝ) (c : ℕ), 0 < γ ∧ 0 < a ∧ 1 ≤ c ∧
      ∀ n : ℕ, 2 ≤ n →
        ∃ g : Fin c → EvenPerm (Fin n), ExpanderWitness g γ a := by sorry

end AESIndependence.Main
