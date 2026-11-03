-- Prove2me | Theorems.Thm_BaconThesis_Collective_eq_C_8
-- name    : BaconThesis.Collective.eq_C_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:14:44.524656+00:00
-- url     : https://prove2.me/theorems/ebcadfd4-0675-428b-b59d-4d8578819df6
-- title:
--   Eq. (C.8) — $(S^{[k]})^2=k(1-k/4)I+\tfrac12\sum_{i\neq j}E_{ij}$
-- statement:
--   For $k$ qubits, the total angular momentum $(S^{[k]})^2=(S^{[k]}_x)^2+(S^{[k]}_y)^2+(S^{[k]}_z)^2$ is a combination of exchange operators and the identity:
--   $$
--   \big(S^{[k]}\big)^2=k\Big(1-\frac k4\Big)I+\frac12\sum_{\substack{i,j=1\\ i\neq j}}^{k}E_{ij},
--   $$
--   the sum running over ordered pairs of distinct qubits, with $E_{ij}$ the exchange (swap) of qubits $i$ and $j$. For $k=2$ this reads $(S^{[2]})^2=I+E_{12}$, with eigenvalue $2$ on the triplet and $0$ on the singlet.
--
--   Consequently $(S^{[k]})^2$ is a Hamiltonian available to an exchange-only quantum computer, which the universality proof of Appendix C uses.
--
--   Differences from the source:
--   - encoding: k qubits, Σ_{i≠j=1}^k → n qubits (the variable is named n), double sum over i and j ∈ univ.erase i (ordered pairs); reason: S^[k] is the collective operator on k qubits ((8.31)); renaming the variable changes nothing
--   - generalization: k ≥ 1 qubits → every n ∈ ℕ, including 0; reason: at 0 qubits both sides are 0 on a one-dimensional space; for n ≥ 1 it is the book's statement
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, Appendix C, (C.8), p.248 (PDF p.265)

import Mathlib
import Definitions.Def_BBPSSW_Distill_pauli
import Definitions.Def_BaconThesis_Collective_onQubit
import Definitions.Def_BaconThesis_Collective_collS
import Definitions.Def_BaconThesis_Collective_totalS2
import Definitions.Def_BaconThesis_Collective_exchange

open scoped Matrix

namespace BaconThesis.Collective

/-- **(C.8): `(S^[k])² = k(1 − k/4) I + ½ Σ_{i≠j} E_ij`.**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1, Appendix C, (C.8), p.248 (PDF p.265): "(ii) Every `(S^[k])²` can be written as a sum of
exchange operators and the identity operation. … so that:
`(S^[k])² = k(1 − k/4) I + ½ Σ_{i≠j=1}^k E_ij`."

For every number of qubits `k` (here `n`), the total angular momentum `(S^[n])²` equals
`n(1 − n/4) I + ½ Σ_{i ≠ j} E_ij`, the sum running over ordered pairs of distinct qubits.

**Formalization Note.** `S^[k]` is the collective operator on `k` qubits ((8.31)), so the
statement for every `n` is the book's statement for every `k`. Qubits are indexed from `0`; the
double sum `Σ_{i≠j}` is over ordered pairs (`j ∈ univ.erase i`). -/
theorem eq_C_8 (n : ℕ) :
    totalS2 n =
      ((n : ℂ) * (1 - (n : ℂ) / 4)) • (1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) +
        (1 / 2 : ℂ) • ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, exchange i j := by sorry

end BaconThesis.Collective
