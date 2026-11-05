-- Prove2me | Theorems.Thm_Chi2QEC_photonLoss_hamming_bound
-- name    : Chi2QEC.photonLoss_hamming_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:45:27.245139+00:00
-- url     : https://prove2.me/theorems/b8a0e731-538c-42f2-86f9-c378128f0130
-- title:
--   Theorem 5 — photon-loss quantum Hamming bound (corrected: $q\ge2$)
-- statement:
--   Let $n\ge0$ and $q\ge2$, and let $C\subseteq\mathcal H_{q-1}^{\otimes n}$ be a code of $n$ physical qudits of dimension $q$ encoding $k$ logical qudits of dimension $b$, so that $\dim C=b^k$. If $C$ satisfies the error-correction condition (23) for the $1+3n$ single-photon-loss errors $\{\hat I\}\cup\{\hat a_{\ell,k'}\}$, then
--   $$
--   (1+3n)\,b^k\le(4q-3)^n.
--   $$
--
--   This is the generalized quantum Hamming bound for single-photon loss. It shows that restricting a code to the pump-photon subspace, and protecting only against photon loss, allows far fewer physical qudits than the bound for arbitrary qudit-rotation errors.
--
--   **Formalization Note** No nondegeneracy is assumed. Taking $b=\dim C$ and $k=1$ gives the bound for every code dimension. The truncated subtraction $4q-3$ is exact under $q\ge2$.
--
--   Differences from the source:
--   - correction: no lower bound on q → 2 ≤ q; reason: false at q = 1: for n = 1, b = k = 1 and C = H_0 = Span{|0,0,0⟩}, (23) holds since C is one-dimensional, but (1 + 3)·1 = 4 > 1 = (4 − 3)¹; every code of the paper has q ≥ 2 (p.17)
--   - generalization: "χ(2) QEC codes that use n physical qudits of dimension q" → any subspace C ≤ pumpSubspace n q; reason: the proof: "each physical qudit comes from a code subspace that lies within H_{q−1}", so every χ(2) QEC code is such a subspace and the statement specializes to them; no product structure or symmetry operator is assumed
--   - reading: a code correcting single-photon loss errors → SatisfiesKL C (lossError n q), i.e. (23) for {I} ∪ {a_{ℓ,k}}; reason: (23) is the paper's correctability condition, and I and the a_{ℓ,k} are the lowest order of (20)–(21) up to the scalar √γ, the 1 + 3n errors of (112)
--   - encoding: k logical qudits of dimension b → finrank C = b ^ k; reason: the code space of k qudits of dimension b has dimension bᵏ
--   - encoding: (23) on logical basis states → (23) for all vectors of C; reason: equivalent by sesquilinearity
--   - encoding: Fock states |n_s, n_i, n_p⟩ with unbounded photon numbers → FockIdx n q, photon numbers truncated at q − 1, modes s, i, p = 0, 1, 2; reason: annihilation never raises a photon number, so every vector, inner product and dimension in the statement is unchanged
-- source:
--   Niu–Chuang–Shapiro, Hardware-Efficient Bosonic QEC Codes Based on Symmetry Operators, arXiv:1709.05302v1, Theorem 5, p.17

import Mathlib
import Definitions.Def_Chi2QEC_lossError
import Definitions.Def_Chi2QEC_pumpSubspace
import Definitions.Def_Chi2QEC_SatisfiesKL

namespace Chi2QEC

/-- Niu–Chuang–Shapiro, *Hardware-Efficient Bosonic QEC Codes Based on Symmetry Operators*,
arXiv:1709.05302v1, Theorem 5, p.17 (corrected: `q ≥ 2`): a code `C` in `H_{q-1}^{⊗n}` of dimension
`bᵏ` (`k` logical qudits of dimension `b`) that satisfies the error-correction condition (23) for
the `1 + 3n` single-photon-loss errors obeys `(1 + 3n) bᵏ ≤ (4q - 3)ⁿ`.

**Formalization Note.** The page has no lower bound on `q`, and the printed statement fails at
`q = 1`: for `n = 1`, `b = k = 1` and `C = H_0`, (23) holds but `4 > 1`. Every code of the paper
has `q ≥ 2`. No nondegeneracy is assumed: the page assumes none and the bound holds without it.
The truncated `4 * q - 3` is exact under `2 ≤ q`. Taking `b = dim C`, `k = 1` gives the bound for
every code dimension. -/
theorem photonLoss_hamming_bound (n q b k : ℕ) (hq : 2 ≤ q)
    (C : Submodule ℂ (EuclideanSpace ℂ (FockIdx n q))) (hC : C ≤ pumpSubspace n q)
    (hdim : Module.finrank ℂ C = b ^ k) (hKL : SatisfiesKL C (lossError n q)) :
    (1 + 3 * n) * b ^ k ≤ (4 * q - 3) ^ n := by sorry

end Chi2QEC
