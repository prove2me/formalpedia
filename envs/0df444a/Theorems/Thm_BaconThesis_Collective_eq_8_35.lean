-- Prove2me | Theorems.Thm_BaconThesis_Collective_eq_8_35
-- name    : BaconThesis.Collective.eq_8_35
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:14:17.217067+00:00
-- url     : https://prove2.me/theorems/9653038e-a190-4781-8a71-695015bddbb0
-- title:
--   Eq. (8.35) — $\dim\mathrm{DFS}_n(h)=\binom nh$, and $\mathrm{DFS}_n(h)$ is the $S_z$ eigenspace
-- statement:
--   For $n$ qubits and $h\in\mathbb N$, let $\mathrm{DFS}_n(h)$ be the span of the computational basis states of Hamming weight $h$ (Definition 8.5.1). Then
--   1. $\displaystyle \dim\mathrm{DFS}_n(h)=\binom nh$;
--   2. $\mathrm{DFS}_n(h)$ is exactly the eigenspace of $S_z=\sum_i\tfrac12\sigma_z^{(i)}$ for the eigenvalue $\tfrac12(n-2h)$:
--   $$
--   \mathrm{DFS}_n(h)=\{\,\psi : S_z\psi=\tfrac12(n-2h)\,\psi\,\}.
--   $$
--
--   Part 2 is the identification, stated on the same page, of the weak collective decoherence DF subspaces with the Hamming-weight classes (the DF subspace criterion is $S_z|\psi\rangle=c|\psi\rangle$); part 1 counts their dimensions (Table 8.1).
--
--   Differences from the source:
--   - generalization: dim(DFS_n(h)) = C(n, h) → the dimension formula and DFS_n(h) = the S_z eigenspace for (n − 2h)/2; reason: the eigenspace identification is the page's own claim ("the DF subspaces correspond to states with equal Hamming weight"); the first conjunct is (8.35)
--   - generalization: 0 ≤ h ≤ n → every h ∈ ℕ; reason: for h > n both subspaces are {0} and C(n, h) = 0; for h ≤ n it is the book's statement
--   - generalization: n qubits, n ≥ 1 (the book starts at n = 1, (8.44)) → every n ∈ ℕ, including n = 0; reason: at n = 0 the space is one-dimensional and every collective operator is 0, where the statement also holds; for n ≥ 1 it is the book's statement
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, Definition 8.5.1 and (8.35), §8.5, p.115 (PDF p.132)

import Mathlib
import Definitions.Def_BBPSSW_Distill_pauli
import Definitions.Def_BaconThesis_Collective_onQubit
import Definitions.Def_BaconThesis_Collective_collS
import Definitions.Def_BaconThesis_Collective_hammingWeight
import Definitions.Def_BaconThesis_Collective_dfsWeak

open scoped Matrix

namespace BaconThesis.Collective

/-- **(8.35): `dim DFS_n(h) = C(n, h)`, and `DFS_n(h)` is the `S_z` eigenspace.**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1, §8.5, Definition 8.5.1 and (8.35), p.115 (PDF p.132): "The dimension of a given `DFS_n(h)`
is given by the number of ways a n bit number can be written which has a Hamming distance h. This
is given by `dim(DFS_n(h)) = n_h = (n choose h)`." The same page identifies the DF subspaces with
the states of equal Hamming weight, on which `S_z` acts as the scalar `½(n − 2h)`.

For all `n` and `h`: the span `DFS_n(h)` of the basis states of Hamming weight `h` has dimension
`C(n, h)`, and it is exactly the eigenspace of `S_z^[n]` for the eigenvalue `(n − 2h)/2`.

**Formalization Note.** The book has `0 ≤ h ≤ n`; for `h > n` both sides are `0` and the
statement still holds. `S_z` acts on `ℂ^(Fin n → Fin 2)` through `Matrix.toLin'`. -/
theorem eq_8_35 (n h : ℕ) :
    Module.finrank ℂ (dfsWeak n h) = n.choose h ∧
      dfsWeak n h =
        Module.End.eigenspace (Matrix.toLin' (collS n .z)) (((n : ℂ) - 2 * (h : ℂ)) / 2) := by sorry

end BaconThesis.Collective
