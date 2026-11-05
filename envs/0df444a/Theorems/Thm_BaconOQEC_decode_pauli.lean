-- Prove2me | Theorems.Thm_BaconOQEC_decode_pauli
-- name    : BaconOQEC.decode_pauli
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:25:59.325833+00:00
-- url     : https://prove2.me/theorems/c38e9f24-fb6e-4bde-8f2b-193fb779e31e
-- title:
--   Combined $X$/$Z$ recovery maps every error of weight $\le\lfloor (n-1)/2\rfloor$ into $\mathcal T$
-- statement:
--   Let $n\ge1$, let $P(a,b)$ be a Pauli error, and let $i_0$, $j_0$ be any row and column. Apply the combined recovery for the measured syndrome of $P(a,b)$: the $X$-correction on row $i_0$, decoded from the $S^Z$-syndrome, and the $Z$-correction (24) on column $j_0$, decoded from the $S^X$-syndrome. Write $(a',b')$ for the bit matrices of the product (up to phase). Then $P(a',b')\in\mathcal T$, i.e. $e(a') = f(b') = 0$, in either of these cases:
--
--   1. $H(e(a))\le\lfloor (n-1)/2\rfloor$ and $H(f(b))\le\lfloor (n-1)/2\rfloor$;
--   2. in particular, $P(a,b)$ has weight at most $\lfloor (n-1)/2\rfloor$.
--
--   This is the Pauli-level content of "an analogous argument holds for Pauli $X$ errors … Pauli $Y$ errors are taken care of by the combined action of these two procedures".
--
--   Differences from the source:
--   - encoding: lattice size n, rows and columns indexed 1..n, generators indexed by Z_{n−1} → n = m + 1 with m : ℕ; rows and columns Fin (m + 1), 0-based; generators indexed by Fin m acting on i.castSucc, i.succ; reason: Lean convention; n = 0 has no qubits, so every lattice of the paper is an instance
--   - encoding: Pauli operators with phases ±1, ±i (the (−1)^φ of (8), (13)) → pairs (a, b) of bit matrices modulo phase; multiplication is addition, commutation is the symplectic bit symp; reason: membership in T, S, C(S), commutation and weight do not depend on the phase
--   - encoding: f″ = the one of f′, ¬f′ with the smallest Hamming weight (tie unspecified) → repDecode returns f′ on a tie H(f′) = H(¬f′); reason: the page leaves ties open; a tie needs H(f) = n/2 > ⌊(n−1)/2⌋, so no instance within the correction radius changes
--   - reading: "an analogous argument holds for Pauli X errors … Pauli Y errors are taken care of by the combined action" → for every Pauli P(a,b) with H(e(a)), H(f(b)) ≤ ⌊(n−1)/2⌋ (in particular weight ≤ ⌊(n−1)/2⌋) the combined recovery yields an element of T; reason: the paper states the X and Y cases in words; this is the combined claim for all Pauli errors in the correction radius
-- source:
--   D. Bacon, Operator Quantum Error Correcting Subsystems for Self-Correcting Quantum Memories, arXiv:quant-ph/0506023v4, §IV.C, p.8

import Mathlib
import Definitions.Def_BaconOQEC_InT
import Definitions.Def_BaconOQEC_weight
import Definitions.Def_BaconOQEC_syndOf
import Definitions.Def_BaconOQEC_recX
import Definitions.Def_BaconOQEC_recZ

namespace BaconOQEC

/-- Bacon, *Operator Quantum Error Correcting Subsystems for Self-Correcting Quantum Memories*,
arXiv:quant-ph/0506023v4, §IV.C, p.8: "Clearly an analogous argument holds for Pauli X errors (with
the role of the rows and columns reversed.) Further, Pauli Y errors are taken care of by the
combined action of these two procedures." For every Pauli error `P(a, b)` and all `i₀`, `j₀`, the
combined recovery (the `X`-correction on row `i₀` decoded from the `S^Z`-syndrome and the
`Z`-correction (24) on column `j₀` decoded from the `S^X`-syndrome) maps `P(a, b)` into `T`
(`e(a') = f(b') = 0`):
1. whenever `H(e(a)) ≤ ⌊(n−1)/2⌋` and `H(f(b)) ≤ ⌊(n−1)/2⌋`;
2. in particular whenever `P(a, b)` has weight at most `⌊(n−1)/2⌋`.

**Formalization Note.** `n = m + 1`, `⌊(n − 1)/2⌋ = m / 2`; `H` is `hammingNorm`; `e = colPar`,
`f = rowPar`. Multiplying Pauli operators adds their bit matrices (up to phase). Indices 0-based. -/
theorem decode_pauli (m : ℕ) (a b : Bits m) (i0 j0 : Fin (m + 1)) :
    (hammingNorm (colPar a) ≤ m / 2 → hammingNorm (rowPar b) ≤ m / 2 →
      InT (a + recX (syndOf a b) i0) (b + recZ (syndOf a b) j0)) ∧
    (weight a b ≤ m / 2 → InT (a + recX (syndOf a b) i0) (b + recZ (syndOf a b) j0)) := by sorry

end BaconOQEC
