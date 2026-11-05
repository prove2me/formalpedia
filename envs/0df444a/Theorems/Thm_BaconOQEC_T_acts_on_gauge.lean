-- Prove2me | Theorems.Thm_BaconOQEC_T_acts_on_gauge
-- name    : BaconOQEC.T_acts_on_gauge
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:26:17.978479+00:00
-- url     : https://prove2.me/theorems/7953c86d-a78d-40cc-9a3a-c97862e55191
-- title:
--   Errors in $\mathcal T$ act only on the gauge subsystem
-- statement:
--   Let $n\ge1$ and let $P(a,b)$ be a Pauli error with all column parities $e_j(a) = 0$ and all row parities $f_i(b) = 0$, i.e. $P(a,b)\in\mathcal T$. Then $P(a,b)$
--
--   1. commutes with every syndrome projector $\Pi_s$ (it is block diagonal for the decomposition (14)), and
--   2. commutes with the logical operators $\bar X = \prod_j X_{1,j}$ and $\bar Z = \prod_i Z_{i,1}$.
--
--   So $P(a,b)$ acts on each sector as $E_{s^X,s^Z}(a,b)\otimes I_2$: it changes only the gauge subsystem and leaves the encoded qubit untouched. This is why the recovery only has to bring an error into $\mathcal T$.
--
--   Differences from the source:
--   - encoding: lattice size n, rows and columns indexed 1..n, generators indexed by Z_{n−1} → n = m + 1 with m : ℕ; rows and columns Fin (m + 1), 0-based; generators indexed by Fin m acting on i.castSucc, i.succ; reason: Lean convention; n = 0 has no qubits, so every lattice of the paper is an instance
--   - encoding: Pauli operators with phases ±1, ±i (the (−1)^φ of (8), (13)) → pairs (a, b) of bit matrices modulo phase; multiplication is addition, commutation is the symplectic bit symp; reason: membership in T, S, C(S), commutation and weight do not depend on the phase
--   - reading: P(a,b) = ⊕_{s^X,s^Z} E_{s^X,s^Z}(a,b) ⊗ I_2 under the decomposition (16) → P(a,b) commutes with every Π_s, with X̄ and with Z̄; reason: (16) is fixed only up to a unitary on each sector; on a sector, X̄ and Z̄ generate the logical M₂(ℂ), whose commutant is exactly the operators E ⊗ I₂
-- source:
--   D. Bacon, Operator Quantum Error Correcting Subsystems for Self-Correcting Quantum Memories, arXiv:quant-ph/0506023v4, §IV.C, eqs. (20)–(21), p.7

import Mathlib
import Definitions.Def_BaconOQEC_InT
import Definitions.Def_BaconOQEC_syndProj
import Definitions.Def_BaconOQEC_Xbar
import Definitions.Def_BaconOQEC_Zbar

open QAlgorithms

namespace BaconOQEC

/-- Bacon, *Operator Quantum Error Correcting Subsystems for Self-Correcting Quantum Memories*,
arXiv:quant-ph/0506023v4, §IV.C, eqs. (20)–(21), p.7: "Notice that if e_j = f_i = 0, ∀i, j, then this
implies that P(a, b) is in the set T. Further note that in this case, the effect of P(a, b) is to
only act on the H^T_{s^X,s^Z} subsystems, i.e. P(a, b) is block diagonal under our subsystem
decomposition, Eq. (16), acting as P(a, b) = ⊕ E_{s^X,s^Z}(a, b) ⊗ I₂." If all column parities of `a`
and all row parities of `b` vanish, then `P(a, b)` commutes with every syndrome projector `Π_s` (it
is block diagonal) and with the logical operators `X̄` and `Z̄` (it acts trivially on the encoded
qubit).

**Formalization Note.** Indices are 0-based (`Fin (m + 1)`, lattice size `n = m + 1`, so `n ≥ 1`); Pauli operators
modulo phase are pairs `(a, b)` of bit matrices. "Acts as `E ⊗ I₂`" is stated without choosing the decomposition
(16): it is commutation with the `Π_s` and with `X̄` (row `0` of `X`) and `Z̄` (column `0` of `Z`),
which generate the logical operator algebra on each sector. -/
theorem T_acts_on_gauge (m : ℕ) (a b : Bits m) (h : InT a b) :
    (∀ s : (Fin m → ZMod 2) × (Fin m → ZMod 2),
      pauliXZ a b * syndProj s = syndProj s * pauliXZ a b) ∧
    pauliXZ a b * Xbar = Xbar * pauliXZ a b ∧
    pauliXZ a b * Zbar = Zbar * pauliXZ a b := by sorry

end BaconOQEC
