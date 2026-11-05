-- Prove2me | Theorems.Thm_Chi2QEC_singleQudit_corrupted_finrank
-- name    : Chi2QEC.singleQudit_corrupted_finrank
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:45:26.052777+00:00
-- url     : https://prove2.me/theorems/29fc0692-6466-44dc-a097-6f937ba6be20
-- title:
--   Proof of Theorem 5 — one qudit: new dimensions per state, total $4q-3$
-- statement:
--   Let $q\ge1$ and let $\mathcal H_{q-1}'$ be the corrupted code subspace of $\mathcal H_{q-1}$ for one qudit, the span of $\mathcal H_{q-1}$ and its images under the single-photon losses. Then
--   $$
--   \dim\mathcal H_{q-1}'=4q-3.
--   $$
--   Moreover, for $q\ge2$, the loss of a single photon from a basis state adds to $\mathcal H_{q-1}$:
--
--   1. one new dimension for $|0,0,q-1\rangle$;
--   2. two new dimensions for $|q-1,q-1,0\rangle$;
--   3. three new dimensions for $|j,j,q-1-j\rangle$ with $1\le j\le q-2$.
--
--   The total is the count $q+3(q-2)+1+2=4q-3$. The case $q=3$ is the nine-dimensional space $\mathcal H_2'$ of (110).
--
--   Differences from the source:
--   - generalization: the total for a qudit of dimension q ≥ 2 → the total for every q ≥ 1; reason: it specializes at q ≥ 2; at q = 1 the only state |0,0,0⟩ is killed by every loss and the dimension is 1 = 4 − 3
--   - reading: the total, used but not written: "(4q − 3)ⁿ" from the three per-state counts → finrank (corruptedSubspace (pumpSubspace 1 q) (lossError 1 q)) = 4 * q - 3; reason: q + 3(q − 2) + 1 + 2 = 4q − 3 is the count that gives the base of the last sentence of the proof
--   - reading: "corrupts H_{q−1} by adding N new dimensions" → finrank (pumpSubspace 1 q ⊔ corruptedSubspace (span {ket x}) (lossError 1 q)) = q + N; reason: the span of H_{q−1} and the loss images of the state has dimension q + N
--   - encoding: Fock states |n_s, n_i, n_p⟩ with unbounded photon numbers → FockIdx n q, photon numbers truncated at q − 1, modes s, i, p = 0, 1, 2; reason: annihilation never raises a photon number, so every vector, inner product and dimension in the statement is unchanged
-- source:
--   Niu–Chuang–Shapiro, Hardware-Efficient Bosonic QEC Codes Based on Symmetry Operators, arXiv:1709.05302v1, proof of Theorem 5, p.17; (110), p.16

import Mathlib
import Definitions.Def_Chi2QEC_lossError
import Definitions.Def_Chi2QEC_pumpSubspace
import Definitions.Def_Chi2QEC_corruptedSubspace

namespace Chi2QEC

/-- Niu–Chuang–Shapiro, *Hardware-Efficient Bosonic QEC Codes Based on Symmetry Operators*,
arXiv:1709.05302v1, proof of Theorem 5, p.17: "For 1 ≤ j ≤ q − 2, loss of a single photon from
|j, j, q − 1 − j⟩ corrupts H_{q−1} by adding three new dimensions., whereas loss of a single photon
from |0, 0, q − 1⟩ corrupts H_{q−1} by adding one new dimension, and loss of a single photon from
|q − 1, q − 1, 0⟩ corrupts H_{q−1} by adding two new dimensions." The second clause is that
per-state count, for `q ≥ 2`; the first clause is the total `q + 3(q - 2) + 1 + 2 = 4q - 3`, the
dimension of the space `H'_{q-1}`, whose `q = 3` instance is (110), p.16.

**Formalization Note.** `n = 1`, so `x 0 0` is the signal photon number `j` of `x`. The total is
stated for `q ≥ 1`: at `q = 1` the only state `|0,0,0⟩` is killed by every loss and the dimension
is `1 = 4 - 3`. The per-state clause needs `q ≥ 2`, as then `|0, 0, q - 1⟩` and
`|q - 1, q - 1, 0⟩` are different states. The `ℕ` subtractions are exact under the hypotheses. -/
theorem singleQudit_corrupted_finrank (q : ℕ) (hq : 1 ≤ q) :
    Module.finrank ℂ (corruptedSubspace (pumpSubspace 1 q) (lossError 1 q)) = 4 * q - 3 ∧
    (2 ≤ q → ∀ x ∈ pumpIndex 1 q,
      Module.finrank ℂ ↥(pumpSubspace 1 q ⊔
          corruptedSubspace (Submodule.span ℂ {EuclideanSpace.single x (1 : ℂ)}) (lossError 1 q)) =
        q + (if (x 0 0 : ℕ) = 0 then 1 else if (x 0 0 : ℕ) = q - 1 then 2 else 3)) := by sorry

end Chi2QEC
