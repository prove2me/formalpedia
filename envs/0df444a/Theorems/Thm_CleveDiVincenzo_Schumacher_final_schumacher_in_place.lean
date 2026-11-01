-- Prove2me | Theorems.Thm_CleveDiVincenzo_Schumacher_final_schumacher_in_place
-- name    : CleveDiVincenzo.Schumacher.final_schumacher_in_place
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:22:16.373613+00:00
-- url     : https://prove2.me/theorems/b2926d9c-f938-4379-8f7f-76352188790c
-- title:
--   §III C, pp.17–19 — FINAL_SCHUMACHER and its inverse compute Schumacher coding in place, restoring $S$ to 0 (corrected: restore loop S ≤ m)
-- statement:
--   For every $n\ge0$ and every $n$-bit string $x$ ($0\le x<2^n$):
--
--   1. the program FINAL_SCHUMACHER (p.19, restore loop corrected), run on $|X,S\rangle=|x,0\rangle$, ends in
--   $$
--   |X,S\rangle=|f(x),\,0\rangle ;
--   $$
--   2. the program FINAL_SCHUMACHER_INVERSE (p.18, restore loop corrected), run on $|X,S\rangle=|f(x),0\rangle$, ends in
--   $$
--   |X,S\rangle=|x,\,0\rangle .
--   $$
--
--   Here $f$ is the Schumacher coding function of Eq. (6). The coding and its inverse are thus computed in place on the data register, with the work register $S$ initialized and finalized to $0$, so that the programs act on superpositions of basis states as the permutation $f$ and its inverse, as Schumacher's quantum data compression requires.
--
--   Differences from the source:
--   - correction: restore loop "if S ≥ m" in FINAL SCHUMACHER INVERSE (p.18) and FINAL SCHUMACHER (p.19) → if S ≤ m in both programs; reason: the loop must leave X = I[x,n,m] = y − Σ_{i<S} C(n,i) (p.17); counterexample n = 1, x = 0, f(0) = 0: the printed FINAL SCHUMACHER INVERSE maps (0, 0) to (−2, 0) and the printed FINAL SCHUMACHER maps (0, 0) to (1, −1), both checked in Lean
--   - correction: S : ⌈log n⌉-bit register → S : ℤ; reason: S reaches the weight m ≤ n, which ⌈log n⌉ bits cannot hold: n = 1, x = 1 needs S = 1 in 0 bits
--   - reading: "In the final pass through the p loop, the occurrence of the zero index in TRUNC_0(X) indicates that the comparison should not be performed at all" (p.18) → TRUNC_0(X) = X mod 1 = 0, so the final-pass condition is S = i and 0 ≥ C(0, i); reason: read as "no quantum comparison is needed" (its outcome is fixed); the other reading, "the condition is false", never sets bit 0 and fails already for n = 1, x = 1
--   - encoding: an n-bit string x_{n−1} … x_0 (x_{n−1} first, x_p the p-th bit) → the natural number x < 2^n, with x_k = Nat.testBit x k; reason: p.6 and Eq. (11), p.9: the string is the binary number; same strings
--   - reading: "preserve lexicographical ordering within each block" (p.8) → index n x = number of z < 2^n with weight z = weight x and z < x (numerical order); reason: for fixed-length strings written most significant bit first, lexicographic order is numerical order; Eqs. (7)–(9) and (11) use this order
--   - encoding: X : n-bit signed arithmetic register; X_j the j-th bit; X_j ← X_j ⊕ 1; TRUNC_j(X) the value of bits 0 … j−1 → X : ℤ; X_j = Int.testBit X j (two's complement); X_j ← X_j ⊕ 1 is X ∓ 2^j; TRUNC_j(X) = X mod 2^j; reason: along every run X stays in [−2^n, 2^n) and S in [0, n] (simulated for n ≤ 8), where ℤ arithmetic and two's-complement bits agree with the (n+1)-bit signed register of p.16; no wrap-around occurs
--   - encoding: pseudocode with classical for loops (for a = s to t, for a = t down to s, both ends included) → the list of statements in execution order (one element per pseudocode line), run by left fold; reason: the loops have constant ranges; unrolling them is the paper's own first compilation step (p.20); same execution
--   - encoding: quantum registers in superposition; the program as a unitary → the program's action on basis states (integer register values); reason: the map is classical, "definite binary-number states are mapped to other definite binary-number states" (p.7); the unitary of a classical reversible program is its permutation of basis states and acts on superpositions by linearity (p.33)
--   - encoding: input y (an n-bit value), output f^{−1}(y) (second clause) → input f(x) for an n-bit string x, output x; reason: f is a bijection of {0, …, 2^n − 1} (§III B, p.13), so every n-bit y is f(x) for exactly one x and f^{−1}(y) = x; same instances
--   - generalization: n ≥ 1 implicitly (n qubits) → every n : ℕ, including n = 0; reason: the n ≥ 1 cases are exactly the paper's claim; n = 0 (one empty string) holds as well
-- source:
--   Cleve, DiVincenzo, Schumacher's quantum data compression as a quantum computation, arXiv:quant-ph/9603009v1, §III C, pp.17–19: FINAL SCHUMACHER INVERSE p.18, FINAL SCHUMACHER p.19 ("the direct function is literally just the time-reverse"), in-place requirement Eqs. (15)–(16), p.13

import Mathlib
import Definitions.Def_CleveDiVincenzo_Schumacher_schumacher
import Definitions.Def_CleveDiVincenzo_Schumacher_trunc
import Definitions.Def_CleveDiVincenzo_Schumacher_finalProg

namespace CleveDiVincenzo.Schumacher

/-- **FINAL_SCHUMACHER and FINAL_SCHUMACHER_INVERSE compute the Schumacher bijection in place**
(Cleve, DiVincenzo, *Schumacher's quantum data compression as a quantum computation*,
arXiv:quant-ph/9603009v1, §III C, pp.17–19; FINAL_SCHUMACHER_INVERSE p.18, FINAL_SCHUMACHER
p.19). For every `n` and every `n`-bit string `x` (`0 ≤ x < 2^n`):
1. FINAL_SCHUMACHER run on `(X, S) = (x, 0)` ends in `(f(x), 0)`;
2. FINAL_SCHUMACHER_INVERSE run on `(X, S) = (f(x), 0)` ends in `(x, 0)`.
Here `f` is the Schumacher coding function of Eq. (6). The computation is done "in-place" on
the data register `X`, and the work register `S` is initialized and finalized to `0`.

**Formalization Note** Both programs are the printed ones, statement by statement, except the
restore loop's `if S ≥ m`, corrected to `if S ≤ m` (with the printed condition both clauses
fail for `n = 1`, `x = 0`). Registers are integers: `X_j` is the two's-complement bit,
`TRUNC_j(X) = X mod 2^j` (so `TRUNC_0(X) = 0`), and `X_j ← X_j ⊕ 1` is `± 2^j`; `S`'s printed
`⌈log n⌉`-bit width is dropped. Basis states only: the unitary of a classical reversible
program is its permutation of basis states (p.7, p.33). Every `n`, including `n = 0`. -/
theorem final_schumacher_in_place (n x : ℕ) (hx : x < 2 ^ n) :
    run (finalProg n) ((x : ℤ), (0 : ℤ)) = ((schumacher n x : ℤ), 0) ∧
      run (finalInverseProg n) ((schumacher n x : ℤ), (0 : ℤ)) = ((x : ℤ), 0) := by sorry

end CleveDiVincenzo.Schumacher
