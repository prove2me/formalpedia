-- Prove2me | Theorems.Thm_BaconOQEC_logical_ops
-- name    : BaconOQEC.logical_ops
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:26:24.220509+00:00
-- url     : https://prove2.me/theorems/e8034fcb-1812-42be-a7c0-7a9878261bc0
-- title:
--   $\bar X$ (a row of $X$) and $\bar Z$ (a column of $Z$) are the logical Pauli operators
-- statement:
--   Let $n\ge1$, $\bar X = \prod_{j=1}^n X_{1,j}$ and $\bar Z = \prod_{i=1}^n Z_{i,1}$. Then:
--
--   1. $\bar X\bar Z = -\bar Z\bar X$, $\bar X^2 = I$ and $\bar Z^2 = I$, so they act as a qubit's $X$ and $Z$;
--   2. each of $\bar X$, $\bar Z$ commutes with every stabilizer generator, is not in $\mathcal T$, and has weight $n$;
--   3. each commutes with every syndrome projector $\Pi_s$.
--
--   On each sector they therefore act as $I_{2^{(n-1)^2}}\otimes X$ and $I_{2^{(n-1)^2}}\otimes Z$, as in
--
--   $$
--   \bar X = \bigoplus_{s^X,s^Z} I_{2^{(n-1)^2}}\otimes X,\qquad \bar Z = \bigoplus_{s^X,s^Z} I_{2^{(n-1)^2}}\otimes Z,
--   $$
--
--   and together they generate every Pauli operator on the encoded qubit.
--
--   Differences from the source:
--   - encoding: lattice size n, rows and columns indexed 1..n, generators indexed by Z_{n−1} → n = m + 1 with m : ℕ; rows and columns Fin (m + 1), 0-based; generators indexed by Fin m acting on i.castSucc, i.succ; reason: Lean convention; n = 0 has no qubits, so every lattice of the paper is an instance
--   - encoding: Pauli operators with phases ±1, ±i (the (−1)^φ of (8), (13)) → pairs (a, b) of bit matrices modulo phase; multiplication is addition, commutation is the symplectic bit symp; reason: membership in T, S, C(S), commutation and weight do not depend on the phase
--   - reading: X̄ = ⊕ I_{2^{(n−1)²}} ⊗ X and Z̄ = ⊕ I_{2^{(n−1)²}} ⊗ Z in a suitable labelling of the subsystem → X̄, Z̄ anticommute, square to I, commute with every Π_s and with S, lie outside T, and have weight n; reason: these are the decomposition-free properties that make X̄, Z̄ the encoded Pauli X and Z in some labelling of (16)
-- source:
--   D. Bacon, Operator Quantum Error Correcting Subsystems for Self-Correcting Quantum Memories, arXiv:quant-ph/0506023v4, §IV.D, eqs. (25)–(26), p.8

import Mathlib
import Definitions.Def_BaconOQEC_InT
import Definitions.Def_BaconOQEC_InCS
import Definitions.Def_BaconOQEC_weight
import Definitions.Def_BaconOQEC_syndProj
import Definitions.Def_BaconOQEC_Xbar
import Definitions.Def_BaconOQEC_Zbar

open QAlgorithms

namespace BaconOQEC

/-- Bacon, *Operator Quantum Error Correcting Subsystems for Self-Correcting Quantum Memories*,
arXiv:quant-ph/0506023v4, §IV.D, eqs. (25)–(26), p.8: "X̄ = ∏_{j=1}^n X_{1,j} = ⊕ I_{2^{(n−1)²}} ⊗ X",
"Z̄ = ∏_{i=1}^n Z_{i,1} = ⊕ I_{2^{(n−1)²}} ⊗ Z". "These two operators can then be used to enact any
Pauli operator on the encoded quantum information." The row operator `X̄` and the column operator
`Z̄` are logical Pauli operators of the encoded qubit:
1. `X̄ Z̄ = −Z̄ X̄`, `X̄² = I`, `Z̄² = I` (they act as `X` and `Z` on a qubit);
2. both commute with `S` (with every generator) and lie outside `T`, and each has weight `n`;
3. both commute with every syndrome projector `Π_s` (they act within each sector).

**Formalization Note.** Rows and columns are 0-based: the paper's row 1 and column 1 are row `0` and
column `0`; the bit matrices are `a_{i,j} = [i = 0]` (for `X̄`) and `b_{i,j} = [j = 0]` (for `Z̄`).
`n = m + 1`. -/
theorem logical_ops (m : ℕ) :
    (Xbar (m := m)) * Zbar = -(Zbar * Xbar) ∧ (Xbar (m := m)) * Xbar = 1 ∧
    (Zbar (m := m)) * Zbar = 1 ∧
    InCS (fun i _ => if i = 0 then 1 else 0 : Bits m) 0 ∧
    ¬ InT (fun i _ => if i = 0 then 1 else 0 : Bits m) 0 ∧
    weight (fun i _ => if i = 0 then 1 else 0 : Bits m) 0 = m + 1 ∧
    InCS 0 (fun _ j => if j = 0 then 1 else 0 : Bits m) ∧
    ¬ InT 0 (fun _ j => if j = 0 then 1 else 0 : Bits m) ∧
    weight 0 (fun _ j => if j = 0 then 1 else 0 : Bits m) = m + 1 ∧
    (∀ s : (Fin m → ZMod 2) × (Fin m → ZMod 2), Xbar * syndProj s = syndProj s * Xbar) ∧
    (∀ s : (Fin m → ZMod 2) × (Fin m → ZMod 2), Zbar * syndProj s = syndProj s * Zbar) := by sorry

end BaconOQEC
