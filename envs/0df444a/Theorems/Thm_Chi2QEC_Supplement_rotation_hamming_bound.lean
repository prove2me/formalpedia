-- Prove2me | Theorems.Thm_Chi2QEC_Supplement_rotation_hamming_bound
-- name    : Chi2QEC.Supplement.rotation_hamming_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T03:08:05.435774+00:00
-- url     : https://prove2.me/theorems/15f6b0d3-0090-4f1f-93e2-52f4a737a773
-- title:
--   Theorem 1 — qudit-rotation quantum Hamming bound $\sum_{j=0}^{t}\binom nj(q^2-1)^jb^k\le q^n$
-- statement:
--   Let $n,t,b,k\ge0$ and $q\ge1$. Let $C\subseteq(\mathbb C^q)^{\otimes n}$ be a code of dimension $b^k$, i.e. $k$ logical qudits of dimension $b$ encoded in $n$ physical qudits of dimension $q$. Suppose that $C$ corrects every qudit-rotation error on at most $t$ qudits, that is, it satisfies the error-correction condition (23),
--   $$
--   \langle W_eu,W_fv\rangle=\alpha_{ef}\langle u,v\rangle\qquad(u,v\in C),
--   $$
--   for all generalized Pauli errors $W_e,W_f$ of weight at most $t$, and that $C$ is nondegenerate for these errors (for every unit vector $\psi\in C$ the vectors $W_e\psi$ are linearly independent). Then
--   $$
--   \sum_{j=0}^{t}\binom nj(q^2-1)^j\,b^k\le q^n .
--   $$
--
--   This is the generalized quantum Hamming bound (102) of Niu, Chuang and Shapiro. It allows the logical dimension $b$ to differ from the physical dimension $q$ and reduces to the usual nondegenerate quantum Hamming bound at $b=q=2$.
--
--   **Formalization Note** The Hilbert space is `EuclideanSpace ℂ (Fin n → Fin q)`; `[NeZero q]` states $q\ge1$, which makes $q^2-1$ exact natural-number subtraction.
--
--   Differences from the source:
--   - reading: "[[n log2(q), k log2(b), 2t+1]] code", one that "corrects t-physical-qudit rotation errors" (p.3) → a subspace C of EuclideanSpace ℂ (Fin n → Fin q) with finrank C = b^k satisfying SatisfiesKL C (rotationError n q t); reason: the paper's correctability criterion is condition (23), imposed on the whole error family with cross terms
--   - reading: qudit-rotation errors → the generalized Pauli operators ⊗X^{a_ℓ}Z^{b_ℓ} of weight ≤ t, identity included; reason: the proof decomposes a weight-j error into (q² − 1)ʲ independent error operators; (23) depends only on the span of the family and nondegeneracy is the same for every linearly independent family with that span, so any other operator basis of the weight-≤ t operators gives an equivalent hypothesis
--   - reading: no nondegeneracy hypothesis in the statement → IsNondegenerate C (rotationError n q t); reason: the proof takes the number of "independent error operators" to be the dimension of the errors of each codeword, which is nondegeneracy, and Theorems 2–4, which apply (102), print it; without it the inequality fails for one-dimensional codes (n = t = 1, q = 2, k = 0: 4 ≤ 2), and for degenerate codes of larger dimension the paper gives no argument
--   - encoding: physical qudits of dimension q → [NeZero q]; reason: a qudit has at least one basis state; it makes q² − 1 exact in ℕ
-- source:
--   Niu–Chuang–Shapiro, Hardware-Efficient Bosonic QEC Codes Based on Symmetry Operators, arXiv:1709.05302v1, Theorem 1, eq. (102), p.15

import Mathlib
import Definitions.Def_Chi2QEC_SatisfiesKL
import Definitions.Def_Chi2QEC_IsNondegenerate
import Definitions.Def_Chi2QEC_Supplement_rotationError

namespace Chi2QEC.Supplement

/-- Niu–Chuang–Shapiro, *Hardware-Efficient Bosonic QEC Codes Based on Symmetry Operators*,
arXiv:1709.05302v1, Theorem 1, eq. (102), p.15: the generalized quantum Hamming bound for
qudit-rotation errors. A code `C ≤ (ℂ^q)^{⊗n}` of dimension `bᵏ` (k logical qudits of dimension
`b`) that corrects every qudit-rotation error on at most `t` qudits, and is nondegenerate for
these errors, satisfies
`Σ_{j=0}^{t} C(n, j)(q² − 1)ʲ bᵏ ≤ qⁿ`.

**Formalization Note.** "Corrects t-physical-qudit rotation errors" (Sec. I, p.3) is condition (23)
(`SatisfiesKL`, cross terms included) for the family `rotationError n q t` of generalized Pauli
errors of weight `≤ t`. Nondegeneracy (`IsNondegenerate` for the same family) is not printed in
the theorem and is read from its context: the proof takes the number of "independent error
operators" to be the dimension of the errors of each codeword, which is nondegeneracy, and
Theorems 2–4, which apply (102), are printed for nondegenerate codes. Without it the inequality
fails for one-dimensional codes (`n = t = 1`, `q = 2`, `k = 0`: `4 ≤ 2`). `[NeZero q]` says a
qudit has at least one basis state; it makes `q² − 1` exact natural-number subtraction. Every
`n, t, b, k` is admitted, including `n = 0` and `t > n`. -/
theorem rotation_hamming_bound (n q t b k : ℕ) [NeZero q]
    (C : Submodule ℂ (EuclideanSpace ℂ (QuditIdx n q)))
    (hdim : Module.finrank ℂ C = b ^ k)
    (hKL : SatisfiesKL C (rotationError n q t))
    (hnd : IsNondegenerate C (rotationError n q t)) :
    (∑ j ∈ Finset.range (t + 1), n.choose j * (q ^ 2 - 1) ^ j) * b ^ k ≤ q ^ n := by sorry

end Chi2QEC.Supplement
