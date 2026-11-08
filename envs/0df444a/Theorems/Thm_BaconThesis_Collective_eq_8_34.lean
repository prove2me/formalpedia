-- Prove2me | Theorems.Thm_BaconThesis_Collective_eq_8_34
-- name    : BaconThesis.Collective.eq_8_34
-- status  : Proved
-- author  : @iris
-- created : 2026-11-03T05:14:35.720207+00:00
-- url     : https://prove2.me/theorems/d8d24cf5-6b7f-4584-a315-70a51281a9a5
-- title:
--   Eq. (8.34) — $S_z|i\rangle=\tfrac12(n-2H(i))|i\rangle$
-- statement:
--   Let $|i\rangle$ be a computational basis state of $n$ qubits and $H(i)$ its Hamming weight (the number of $1$'s). Then $|i\rangle$ is an eigenvector of the collective operator $S_z=\sum_{l}\tfrac12\sigma_z^{(l)}$:
--   $$
--   S_z|i\rangle=\tfrac12\big(n-2H(i)\big)|i\rangle .
--   $$
--
--   All basis states of the same Hamming weight therefore share the same $S_z$ eigenvalue, which is why the weak collective decoherence DF subspaces are the Hamming-weight classes.
--
--   Differences from the source:
--   - encoding: |i⟩, i an n-bit number → the standard basis vector of the bit string x : Fin n → Fin 2; reason: same basis
--   - generalization: n qubits, n ≥ 1 (the book starts at n = 1, (8.44)) → every n ∈ ℕ, including n = 0; reason: at n = 0 the space is one-dimensional and every collective operator is 0, where the statement also holds; for n ≥ 1 it is the book's statement
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, (8.34), §8.5, p.115 (PDF p.132)

import Mathlib
import Definitions.Def_BBPSSW_Distill_pauli
import Definitions.Def_BaconThesis_Collective_onQubit
import Definitions.Def_BaconThesis_Collective_collS
import Definitions.Def_BaconThesis_Collective_hammingWeight

open scoped Matrix

namespace BaconThesis.Collective

/-- **(8.34): `S_z|i⟩ = ½(n − 2H(i))|i⟩`.**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1, §8.5, (8.34), p.115 (PDF p.132): "Then this is just `S_z|i⟩ = ½(n − 2H(i))|i⟩`."

For every computational basis state `|x⟩` of `n` qubits, `S_z^[n] |x⟩ = ½(n − 2 H(x)) |x⟩`, where
`H(x)` is the Hamming weight (number of 1's) of `x`.

**Formalization Note.** `|x⟩` is the standard basis vector `Pi.single x 1` of
`ℂ^(Fin n → Fin 2)`; `S_z = collS n .z`. -/
theorem eq_8_34 (n : ℕ) (x : Fin n → Fin 2) :
    collS n .z *ᵥ Pi.single x (1 : ℂ) =
      (((n : ℂ) - 2 * (hammingWeight x : ℂ)) / 2) • Pi.single x (1 : ℂ) := by sorry

end BaconThesis.Collective
