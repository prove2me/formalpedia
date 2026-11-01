-- Prove2me | Theorems.Thm_CleveDiVincenzo_Schumacher_final_inverse_correct
-- name    : CleveDiVincenzo.Schumacher.final_inverse_correct
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:22:22.734962+00:00
-- url     : https://prove2.me/theorems/c6e8a919-db7f-4e61-a1e4-f17ee145a6fb
-- title:
--   §III C, p.18 — FINAL_SCHUMACHER_INVERSE computes $f^{-1}$ in place (corrected: restore loop S ≤ m)
-- statement:
--   For every $n\ge0$ and every $n$-bit string $x$, the program FINAL_SCHUMACHER_INVERSE (p.18, restore loop corrected), run on
--   $$
--   |X,S\rangle=|f(x),\,0\rangle ,
--   $$
--   ends in $|X,S\rangle=|x,\,0\rangle$: the data register holds $f^{-1}(f(x))=x$ and the counter $S$ is finalized to $0$.
--
--   This is the paper's final program for the inverse of the Schumacher coding function, which needs no register besides $X$ and $S$.
--
--   Differences from the source:
--   - correction: restore loop "for m = 0 to n do if S ≥ m then X ← X + C(n,m)" (p.18) → if S ≤ m then X ← X + C(n,m); reason: the loop must leave X = I[x,n,m] = y − Σ_{i<S} C(n,i) (p.17); counterexample n = 1, y = f(0) = 0: the printed FINAL SCHUMACHER INVERSE maps (0, 0) to (−2, 0), checked in Lean
--   - correction: S : ⌈log n⌉-bit register → S : ℤ; reason: S reaches the weight m ≤ n, which ⌈log n⌉ bits cannot hold: n = 1, x = 1 needs S = 1 in 0 bits
--   - reading: "In the final pass through the p loop, the occurrence of the zero index in TRUNC_0(X) indicates that the comparison should not be performed at all" (p.18) → TRUNC_0(X) = X mod 1 = 0, so the final-pass condition is S = i and 0 ≥ C(0, i); reason: read as "no quantum comparison is needed" (its outcome is fixed); the other reading, "the condition is false", never sets bit 0 and fails already for n = 1, x = 1
--   - encoding: an n-bit string x_{n−1} … x_0 (x_{n−1} first, x_p the p-th bit) → the natural number x < 2^n, with x_k = Nat.testBit x k; reason: p.6 and Eq. (11), p.9: the string is the binary number; same strings
--   - reading: "preserve lexicographical ordering within each block" (p.8) → index n x = number of z < 2^n with weight z = weight x and z < x (numerical order); reason: for fixed-length strings written most significant bit first, lexicographic order is numerical order; Eqs. (7)–(9) and (11) use this order
--   - encoding: X : n-bit signed arithmetic register; X_j the j-th bit; X_j ← X_j ⊕ 1; TRUNC_j(X) the value of bits 0 … j−1 → X : ℤ; X_j = Int.testBit X j (two's complement); X_j ← X_j ⊕ 1 is X ∓ 2^j; TRUNC_j(X) = X mod 2^j; reason: along every run X stays in [−2^n, 2^n) and S in [0, n] (simulated for n ≤ 8), where ℤ arithmetic and two's-complement bits agree with the (n+1)-bit signed register of p.16; no wrap-around occurs
--   - encoding: pseudocode with classical for loops (for a = s to t, for a = t down to s, both ends included) → the list of statements in execution order (one element per pseudocode line), run by left fold; reason: the loops have constant ranges; unrolling them is the paper's own first compilation step (p.20); same execution
--   - encoding: quantum registers in superposition; the program as a unitary → the program's action on basis states (integer register values); reason: the map is classical, "definite binary-number states are mapped to other definite binary-number states" (p.7); the unitary of a classical reversible program is its permutation of basis states and acts on superpositions by linearity (p.33)
--   - encoding: input y (an n-bit value), output f^{−1}(y) with S finalized to 0 → input f(x) for an n-bit string x, output x; reason: f is a bijection of {0, …, 2^n − 1} (§III B, p.13), so every n-bit y is f(x) for exactly one x and f^{−1}(y) = x; same instances
--   - generalization: n ≥ 1 implicitly (n qubits) → every n : ℕ, including n = 0; reason: the n ≥ 1 cases are exactly the paper's claim; n = 0 (one empty string) holds as well
-- source:
--   Cleve, DiVincenzo, Schumacher's quantum data compression as a quantum computation, arXiv:quant-ph/9603009v1, §III C, p.18 (program FINAL SCHUMACHER INVERSE and the sentence introducing it)

import Mathlib
import Definitions.Def_CleveDiVincenzo_Schumacher_schumacher
import Definitions.Def_CleveDiVincenzo_Schumacher_trunc
import Definitions.Def_CleveDiVincenzo_Schumacher_finalProg

namespace CleveDiVincenzo.Schumacher

/-- **FINAL_SCHUMACHER_INVERSE computes `f⁻¹` in place** (Cleve, DiVincenzo, *Schumacher's
quantum data compression as a quantum computation*, arXiv:quant-ph/9603009v1, §III C, p.18):
"with one small modification, TRY_INVERSE can be turned into our final program for the inverse
of the Schumacher coding function". For every `n` and every `n`-bit string `x`, running
FINAL_SCHUMACHER_INVERSE (p.18, restore loop corrected) on `(X, S) = (f(x), 0)` ends in
`(x, 0)`: `X` holds `f⁻¹(f(x)) = x` and `S` is finalized to `0`.

**Formalization Note** `finalInverseProg` is the printed program with the second loop's
`if S ≥ m` corrected to `if S ≤ m` (with the printed condition the run from `(0, 0)` for
`n = 1` ends in `(−2, 0)`). `TRUNC_j(X) = X mod 2^j`, also `TRUNC_0(X) = 0` in the final pass.
Registers are integers (`S`'s printed `⌈log n⌉`-bit width is dropped); basis states only. -/
theorem final_inverse_correct (n x : ℕ) (hx : x < 2 ^ n) :
    run (finalInverseProg n) ((schumacher n x : ℤ), (0 : ℤ)) = ((x : ℤ), 0) := by sorry

end CleveDiVincenzo.Schumacher
