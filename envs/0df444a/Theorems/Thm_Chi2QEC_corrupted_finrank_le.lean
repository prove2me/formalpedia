-- Prove2me | Theorems.Thm_Chi2QEC_corrupted_finrank_le
-- name    : Chi2QEC.corrupted_finrank_le
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:45:22.936674+00:00
-- url     : https://prove2.me/theorems/bdd9311d-14e5-4c5e-ba58-63fbcf99b17c
-- title:
--   Proof of Theorem 5 — $D_{\mathrm{loss}}\le(4q-3)^n$
-- statement:
--   Let $C$ be any subspace of $\mathcal H_{q-1}^{\otimes n}$. Then the corrupted code subspace of $C$ under the $1+3n$ single-photon-loss errors has dimension
--   $$
--   D_{\mathrm{loss}}\le(4q-3)^n.
--   $$
--   Together with the count of error images this yields the Hamming bound of Theorem 5 for nondegenerate codes.
--
--   **Formalization Note** The truncated natural-number subtraction gives $4q-3=0$ at $q=0$, where for $n\ge1$ the space is zero. For $n=0$ the Fock space is one-dimensional and the right side is $1$.
--
--   Differences from the source:
--   - generalization: q the dimension of a physical qudit → every n and q, with no hypothesis on q; reason: it specializes to every q ≥ 2; the excluded degenerate values q = 0, 1 satisfy the bound too
--   - reading: D_loss, the dimension of "the corrupted code subspace" → finrank (corruptedSubspace C (lossError n q)); reason: the corrupted code subspace is the span of the images of C under the errors
--   - generalization: "χ(2) QEC code" → any subspace C ≤ pumpSubspace n q; reason: the proof uses only that the code "lies within H_{q−1}" on each qudit, so every χ(2) QEC code is such a subspace and the statement specializes to them
--   - encoding: Fock states |n_s, n_i, n_p⟩ with unbounded photon numbers → FockIdx n q, photon numbers truncated at q − 1, modes s, i, p = 0, 1, 2; reason: annihilation never raises a photon number, so every vector, inner product and dimension in the statement is unchanged
-- source:
--   Niu–Chuang–Shapiro, Hardware-Efficient Bosonic QEC Codes Based on Symmetry Operators, arXiv:1709.05302v1, proof of Theorem 5, "Thus we get D_loss ≤ (4q − 3)ⁿ", p.17

import Mathlib
import Definitions.Def_Chi2QEC_lossError
import Definitions.Def_Chi2QEC_pumpSubspace
import Definitions.Def_Chi2QEC_corruptedSubspace

namespace Chi2QEC

/-- Niu–Chuang–Shapiro, *Hardware-Efficient Bosonic QEC Codes Based on Symmetry Operators*,
arXiv:1709.05302v1, proof of Theorem 5, p.17: "Thus we get D_loss ≤ (4q − 3)ⁿ": the corrupted
code subspace of any code in `H_{q-1}^{⊗n}` has dimension at most `(4q - 3)ⁿ`.

**Formalization Note.** Stated for every `n` and `q`, with no hypothesis on `q`. The truncated
`4 * q - 3` is `0` at `q = 0`, where for `n ≥ 1` the space is zero; for `n = 0` the Fock space is
one-dimensional and the right side is `1`. -/
theorem corrupted_finrank_le (n q : ℕ) (C : Submodule ℂ (EuclideanSpace ℂ (FockIdx n q)))
    (hC : C ≤ pumpSubspace n q) :
    Module.finrank ℂ (corruptedSubspace C (lossError n q)) ≤ (4 * q - 3) ^ n := by sorry

end Chi2QEC
