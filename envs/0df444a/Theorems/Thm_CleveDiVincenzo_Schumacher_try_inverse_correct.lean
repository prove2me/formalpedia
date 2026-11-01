-- Prove2me | Theorems.Thm_CleveDiVincenzo_Schumacher_try_inverse_correct
-- name    : CleveDiVincenzo.Schumacher.try_inverse_correct
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:22:28.943555+00:00
-- url     : https://prove2.me/theorems/7671781e-8a95-41d3-8f8e-9138a163f188
-- title:
--   Eqs. (24)–(25) — TRY_INVERSE maps $|0,y,0\rangle$ to $|f^{-1}(y),0,0\rangle$ (corrected: restore loop S ≤ m)
-- statement:
--   For every $n\ge0$ and every $n$-bit string $x$, the program TRY_INVERSE (p.16, restore loop corrected), run on the input state
--   $$
--   |X,Y,S\rangle=|0,\,f(x),\,0\rangle ,
--   $$
--   ends in the state
--   $$
--   |X,Y,S\rangle=|x,\,0,\,0\rangle .
--   $$
--   So it computes $f^{-1}$ and returns both work registers $Y$ and $S$ to $0$; "with a final transposing of the X and Y registers, we obtain a program that implements the inverse" of the Schumacher coding in place.
--
--   Differences from the source:
--   - correction: restore loop "for m = 0 to n do if S ≥ m then Y ← Y + C(n,m)" (p.16) → if S ≤ m then Y ← Y + C(n,m); reason: the text needs Y = I[x,n,m] = y − Σ_{i<S} C(n,i) after this loop (p.17), the printed condition gives y − Σ_{i>S} C(n,i); counterexample n = 1, y = f(0) = 0: the printed TRY INVERSE maps (0, 0, 0) to (0, −1, 0), checked in Lean
--   - correction: S : ⌈log n⌉-bit register → S : ℤ; reason: S reaches the weight m ≤ n, which ⌈log n⌉ bits cannot hold: n = 1, x = 1 needs S = 1 in 0 bits
--   - encoding: an n-bit string x_{n−1} … x_0 (x_{n−1} first, x_p the p-th bit) → the natural number x < 2^n, with x_k = Nat.testBit x k; reason: p.6 and Eq. (11), p.9: the string is the binary number; same strings
--   - reading: "preserve lexicographical ordering within each block" (p.8) → index n x = number of z < 2^n with weight z = weight x and z < x (numerical order); reason: for fixed-length strings written most significant bit first, lexicographic order is numerical order; Eqs. (7)–(9) and (11) use this order
--   - encoding: X : n-bit register, Y : n-bit signed arithmetic register; X_j the j-th bit; X_j ← X_j ⊕ 1 → X, Y : ℤ; X_j = Int.testBit X j (two's complement); X_j ← X_j ⊕ 1 is X ∓ 2^j; reason: along every run the values stay in [−2^n, 2^n) and S in [0, n] (simulated for n ≤ 8), where ℤ arithmetic and two's-complement bits agree with the (n+1)-bit signed register of p.16; no wrap-around occurs
--   - encoding: pseudocode with classical for loops (for a = s to t, for a = t down to s, both ends included) → the list of statements in execution order (one element per pseudocode line), run by left fold; reason: the loops have constant ranges; unrolling them is the paper's own first compilation step (p.20); same execution
--   - encoding: quantum registers in superposition; the program as a unitary → the program's action on basis states (integer register values); reason: the map is classical, "definite binary-number states are mapped to other definite binary-number states" (p.7); the unitary of a classical reversible program is its permutation of basis states and acts on superpositions by linearity (p.33)
--   - encoding: input y (an n-bit value), output f^{−1}(y) with Y and S returned to 0 → input f(x) for an n-bit string x, output x; reason: f is a bijection of {0, …, 2^n − 1} (§III B, p.13), so every n-bit y is f(x) for exactly one x and f^{−1}(y) = x; same instances
--   - generalization: n ≥ 1 implicitly (n qubits) → every n : ℕ, including n = 0; reason: the n ≥ 1 cases are exactly the paper's claim; n = 0 (one empty string) holds as well
-- source:
--   Cleve, DiVincenzo, Schumacher's quantum data compression as a quantum computation, arXiv:quant-ph/9603009v1, §III C, Eqs. (24)–(25), p.17; program TRY INVERSE, p.16

import Mathlib
import Definitions.Def_CleveDiVincenzo_Schumacher_schumacher
import Definitions.Def_CleveDiVincenzo_Schumacher_trunc
import Definitions.Def_CleveDiVincenzo_Schumacher_finalProg

namespace CleveDiVincenzo.Schumacher

/-- **Eqs. (24)–(25)** (Cleve, DiVincenzo, *Schumacher's quantum data compression as a quantum
computation*, arXiv:quant-ph/9603009v1, §III C, p.17): "on input state
`|X, Y, S⟩ = |0, y, 0⟩`, TRY_INVERSE produces the final state `|X, Y, S⟩ = |f⁻¹(y), 0, 0⟩`".
For every `n` and every `n`-bit string `x`, running TRY_INVERSE (p.16, restore loop corrected)
on `(X, Y, S) = (0, f(x), 0)` ends in `(x, 0, 0)`.

**Formalization Note** Every `y ∈ {0, …, 2^n − 1}` is `f(x)` for exactly one `x < 2^n`
(`schumacher_bijective`), so stating the claim at `y = f(x)` with result `x = f⁻¹(y)` is the
paper's claim for all `y`. `tryInverseProg` is the printed program with the second loop's
`if S ≥ m` corrected to `if S ≤ m`; with the printed condition the claim fails for `n = 1`,
`y = 0`. Registers are integers; basis states only (a classical reversible program acts on
superpositions by linearity, p.7). -/
theorem try_inverse_correct (n x : ℕ) (hx : x < 2 ^ n) :
    run (tryInverseProg n) ((0 : ℤ), (schumacher n x : ℤ), (0 : ℤ)) =
      ((x : ℤ), 0, 0) := by sorry

end CleveDiVincenzo.Schumacher
