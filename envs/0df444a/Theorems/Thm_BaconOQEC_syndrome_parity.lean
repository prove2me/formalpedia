-- Prove2me | Theorems.Thm_BaconOQEC_syndrome_parity
-- name    : BaconOQEC.syndrome_parity
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:26:32.357515+00:00
-- url     : https://prove2.me/theorems/f8a6d634-5b81-4932-9c9b-0011d6d42aa1
-- title:
--   The syndrome reads $f_i(b)\oplus f_{i+1}(b)$ and $e_j(a)\oplus e_{j+1}(a)$
-- statement:
--   Let $n\ge1$ and let $P(a,b)$ be any Pauli error. Then:
--
--   1. $S^X_i\,P(a,b) = (-1)^{f_i(b)\oplus f_{i+1}(b)}\,P(a,b)\,S^X_i$ for $i = 1,\dots,n-1$;
--   2. $S^Z_j\,P(a,b) = (-1)^{e_j(a)\oplus e_{j+1}(a)}\,P(a,b)\,S^Z_j$ for $j = 1,\dots,n-1$;
--   3. hence the syndrome of $P(a,b)$ is
--
--   $$
--   s^X_i = \bigoplus_{j=1}^n (b_{i,j}\oplus b_{i+1,j}) = f_i(b)\oplus f_{i+1}(b),\qquad s^Z_j = \bigoplus_{i=1}^n (a_{i,j}\oplus a_{i,j+1}) = e_j(a)\oplus e_{j+1}(a);
--   $$
--
--   4. $\Pi_s\,P(a,b) = P(a,b)\,\Pi_{s\oplus\sigma(a,b)}$ for every $s$, where $\sigma(a,b)$ is that syndrome: $P(a,b)$ moves the sector with label $s'$ to the sector with label $s'\oplus\sigma(a,b)$.
--
--   So measuring the generators after the error reveals the parity differences of the error strings, which is the syndrome of a repetition code.
--
--   Differences from the source:
--   - encoding: lattice size n, rows and columns indexed 1..n, generators indexed by Z_{n−1} → n = m + 1 with m : ℕ; rows and columns Fin (m + 1), 0-based; generators indexed by Fin m acting on i.castSucc, i.succ; reason: Lean convention; n = 0 has no qubits, so every lattice of the paper is an instance
--   - encoding: syndrome eigenvalues s^X_i, s^Z_i = ±1; code sector s^X = s^Z = {+1}^{n−1} → syndrome bits in ZMod 2, bit 0 ↔ eigenvalue +1, bit 1 ↔ −1; code sector s = 0; reason: Lean convention; the same labels
--   - reading: "measuring S^X_i is equivalent to determining f_i(b) ⊕ f_{i+1}(b)" (and the S^Z analogue) → the commutation sign of S^X_i (S^Z_j) with P(a,b) is (−1)^{f_i ⊕ f_{i+1}} ((−1)^{e_j ⊕ e_{j+1}}), and Π_s P(a,b) = P(a,b) Π_{s ⊕ σ(a,b)}; reason: a measurement of S^X_i after P(a,b) on a sector returns the sector's label times this sign; the statement is the operator identity behind "equivalent to determining"
-- source:
--   D. Bacon, Operator Quantum Error Correcting Subsystems for Self-Correcting Quantum Memories, arXiv:quant-ph/0506023v4, §IV.C, eqs. (22)–(23), p.7

import Mathlib
import Definitions.Def_BaconOQEC_colPar
import Definitions.Def_BaconOQEC_rowPar
import Definitions.Def_BaconOQEC_syndOf
import Definitions.Def_BaconOQEC_syndProj

open QAlgorithms

namespace BaconOQEC

/-- Bacon, *Operator Quantum Error Correcting Subsystems for Self-Correcting Quantum Memories*,
arXiv:quant-ph/0506023v4, §IV.C, eqs. (22)–(23), p.7: "measuring S^X_i is equivalent to determining
⊕_{j=1}^n (b_{i,j} ⊕ b_{i+1,j}) = f_i(b) ⊕ f_{i+1}(b), and similarly measuring S^Z_j is equivalent
to determining ⊕_{i=1}^n (a_{i,j} ⊕ a_{i,j+1}) = e_j(a) ⊕ e_{j+1}(a)." For every Pauli error
`P(a, b)`:
1. `S^X_i P(a, b) = (−1)^{f_i(b) ⊕ f_{i+1}(b)} P(a, b) S^X_i`;
2. `S^Z_j P(a, b) = (−1)^{e_j(a) ⊕ e_{j+1}(a)} P(a, b) S^Z_j`;
3. the syndrome of `P(a, b)` is therefore `(f_i ⊕ f_{i+1})_i`, `(e_j ⊕ e_{j+1})_j`;
4. `Π_s P(a, b) = P(a, b) Π_{s ⊕ σ(a,b)}`, `σ(a, b)` the syndrome: `P(a, b)` maps the sector with
   syndrome `s'` into the sector with syndrome `s' ⊕ σ(a, b)`.

**Formalization Note.** Generators indexed by `Fin m` act on rows (columns) `i.castSucc`, `i.succ`;
indices 0-based, `n = m + 1`. Syndrome bit `0` is eigenvalue `+1`; addition in `ZMod 2` is `⊕`. -/
theorem syndrome_parity (m : ℕ) (a b : Bits m) :
    (∀ i : Fin m, pauliXZ (SX i).1 (SX i).2 * pauliXZ a b =
      ((-1 : ℂ) ^ (rowPar b i.castSucc + rowPar b i.succ).val) •
        (pauliXZ a b * pauliXZ (SX i).1 (SX i).2)) ∧
    (∀ j : Fin m, pauliXZ (SZ j).1 (SZ j).2 * pauliXZ a b =
      ((-1 : ℂ) ^ (colPar a j.castSucc + colPar a j.succ).val) •
        (pauliXZ a b * pauliXZ (SZ j).1 (SZ j).2)) ∧
    syndOf a b = (fun i => rowPar b i.castSucc + rowPar b i.succ,
      fun j => colPar a j.castSucc + colPar a j.succ) ∧
    ∀ s : (Fin m → ZMod 2) × (Fin m → ZMod 2),
      syndProj s * pauliXZ a b = pauliXZ a b * syndProj (s + syndOf a b) := by sorry

end BaconOQEC
