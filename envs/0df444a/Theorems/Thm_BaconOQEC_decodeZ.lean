-- Prove2me | Theorems.Thm_BaconOQEC_decodeZ
-- name    : BaconOQEC.decodeZ
-- status  : Proved
-- author  : @iris
-- created : 2026-11-04T06:25:55.068199+00:00
-- url     : https://prove2.me/theorems/bd2df933-5832-4354-9989-76640642a056
-- title:
--   The $Z$ decoder leaves an all-0 or all-1 string, all-0 when $H(f)\le\lfloor (n-1)/2\rfloor$
-- statement:
--   Let $n\ge1$, let $P(a,b)$ be a Pauli error and let $j_0$ be any column. Decode $f''$ from the measured $S^X$-syndrome of $P(a,b)$ and apply $Q_1(f'') = \prod_i Z_{i,j_0}^{\delta_{f''_i,1}}$ (24). Up to phase the result is $P(a,b')$, with $b'$ equal to $b$ plus the bit matrix of $Q_1(f'')$. Then:
--
--   1. the new $Z$ error string $f(b') = (f_1(b'),\dots,f_n(b'))$ is constant: all zeros or all ones;
--   2. if the Hamming weight of the original string satisfies
--
--   $$
--   H\big(f(b)\big) \le \Big\lfloor \frac{n-1}{2}\Big\rfloor ,
--   $$
--
--   then $f(b') = 0$: the correction succeeds.
--
--   Differences from the source:
--   - encoding: lattice size n, rows and columns indexed 1..n, generators indexed by Z_{n−1} → n = m + 1 with m : ℕ; rows and columns Fin (m + 1), 0-based; generators indexed by Fin m acting on i.castSucc, i.succ; reason: Lean convention; n = 0 has no qubits, so every lattice of the paper is an instance
--   - encoding: Pauli operators with phases ±1, ±i (the (−1)^φ of (8), (13)) → pairs (a, b) of bit matrices modulo phase; multiplication is addition, commutation is the symplectic bit symp; reason: membership in T, S, C(S), commutation and weight do not depend on the phase
--   - encoding: f″ = the one of f′, ¬f′ with the smallest Hamming weight (tie unspecified) → repDecode returns f′ on a tie H(f′) = H(¬f′); reason: the page leaves ties open; a tie needs H(f) = n/2 > ⌊(n−1)/2⌋, so no instance within the correction radius changes
--   - generalization: P(a, b) "consisted of Z errors b" with H(f) ≤ ⌊(n−1)/2⌋ → clause 2 holds for every a, with the same bound on H(f(b)); reason: the string f(b) and the S^X-syndrome depend on b only, so a = 0 is the source's case
-- source:
--   D. Bacon, Operator Quantum Error Correcting Subsystems for Self-Correcting Quantum Memories, arXiv:quant-ph/0506023v4, §IV.C, eq. (24) and p.8

import Mathlib
import Definitions.Def_BaconOQEC_rowPar
import Definitions.Def_BaconOQEC_syndOf
import Definitions.Def_BaconOQEC_recZ

namespace BaconOQEC

/-- Bacon, *Operator Quantum Error Correcting Subsystems for Self-Correcting Quantum Memories*,
arXiv:quant-ph/0506023v4, §IV.C, eq. (24), p.8: "The operator Q₁(f″)P(a, b) is then seen to be of one
of two forms: either this new operator has the Z error string equal to all zeros or all ones. …
If P(a, b) consisted of Z errors b with an error string f_i(b) with a Hamming weight of this string
H(f) which is less than or equal to ⌊(n−1)/2⌋, then the correction procedure will succeed." For every
error `P(a, b)` and every column `j₀`, after the `Z`-correction `Q₁(f″)` computed from the measured
`S^X`-syndrome, the new `Z`-part `b' = b ⊕ (Q₁'s b-matrix)` has
1. a constant row-parity string `f(b')` (all zeros or all ones), and
2. `f(b') = 0` whenever `H(f(b)) ≤ ⌊(n − 1)/2⌋`.

**Formalization Note.** `n = m + 1`, so `⌊(n − 1)/2⌋ = m / 2` (natural division); `H` is Mathlib's
`hammingNorm`. Multiplying Pauli operators adds their bit matrices (up to phase). The syndrome
fed to the decoder is the true syndrome `syndOf a b` of the error, whose `S^X`-part depends on `b`
only. -/
theorem decodeZ (m : ℕ) (a b : Bits m) (j0 : Fin (m + 1)) :
    let b' := b + recZ (syndOf a b) j0
    (∃ c : ZMod 2, ∀ i, rowPar b' i = c) ∧
    (hammingNorm (rowPar b) ≤ m / 2 → ∀ i, rowPar b' i = 0) := by sorry

end BaconOQEC
