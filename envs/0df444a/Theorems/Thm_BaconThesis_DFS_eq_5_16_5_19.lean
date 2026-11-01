-- Prove2me | Theorems.Thm_BaconThesis_DFS_eq_5_16_5_19
-- name    : BaconThesis.DFS.eq_5_16_5_19
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:58:06.379338+00:00
-- url     : https://prove2.me/theorems/dbbeadfe-1bda-4526-ac97-bf550a14260e
-- title:
--   Eqs. (5.16)–(5.19) — a pure state invariant under a trace-preserving OSR is an eigenvector of every OSR operator
-- statement:
--   Let $\{A_i\}$ be a finite family of operators on a finite-dimensional Hilbert space $\mathcal H_S$ satisfying the normalization
--   $$
--   \sum_i A_i^\dagger A_i=I ,
--   $$
--   and let $|j\rangle$ be a unit vector whose pure state is invariant under the operator-sum evolution,
--   $$
--   \sum_i A_i\,|j\rangle\langle j|\,A_i^\dagger=|j\rangle\langle j| .
--   $$
--   Then every $A_i$ maps $|j\rangle$ to a multiple of itself: for each $i$ there is $a_i\in\mathbb C$ with $A_i|j\rangle=a_i|j\rangle$.
--
--   In the thesis this is the necessity half of the proof of Theorem 5.3.1, applied to the OSR operators $A_i(t)$ at a fixed time: decomposing $A_i(t)|j\rangle=a_i(t)|j\rangle+b_i(t)|j_\perp(i)\rangle$, invariance forces $\sum_i|a_i(t)|^2=1$ while normalization gives $\sum_i|a_i(t)|^2+|b_i(t)|^2=1$, so every $b_i(t)=0$.
--
--   **Formalization Note** $|j\rangle\langle j|$ is the rank-one matrix of $j$, and "unit" means $\langle j|j\rangle=1$.
--
--   Differences from the source:
--   - generalization: the OSR operators A_i(t) of a system–environment evolution at time t → any finite family A_i with ∑_i A_i†A_i = I; reason: the argument uses only the invariance (5.11) and the normalization (2.12), which the OSR operators satisfy (milestone eq_2_12)
--   - encoding: a state |j⟩ → a vector j with ⟨j|j⟩ = 1; reason: |j⟩⟨j| is a pure state, so |j⟩ is normalized; same instances
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, proof of Theorem 5.3.1, eqs. (5.16)–(5.19), pp.72–73 (PDF pp.89–90)

import Mathlib

open scoped Matrix

namespace BaconThesis.DFS

/-- **Necessity step, eqs. (5.16)–(5.19): an invariant pure state is an eigenvector of every OSR
operator.**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1,
proof of Theorem 5.3.1, eqs. (5.16)–(5.19), pp.72–73 (PDF pp.89–90): write
`Aᵢ(t)|j⟩ = aᵢ(t)|j⟩ + bᵢ(t)|j_⊥(i)⟩`; invariance `∑ᵢ Aᵢ(t)|j⟩⟨j|Aᵢ†(t) = |j⟩⟨j|` gives
`∑ᵢ|aᵢ(t)|² = 1`, the normalization `∑ᵢ Aᵢ†(t)Aᵢ(t) = I` gives `∑ᵢ|aᵢ(t)|² + |bᵢ(t)|² = 1`, hence
every `bᵢ(t) = 0` and `Aᵢ(t)|j⟩ = aᵢ(t)|j⟩`.

For every finite family of operators `Aᵢ` with `∑ᵢ Aᵢ†Aᵢ = I` and every unit vector `j` with
`∑ᵢ Aᵢ|j⟩⟨j|Aᵢ† = |j⟩⟨j|`, each `Aᵢ j` is a scalar multiple of `j`.

**Formalization Note.** The book applies the argument to the OSR operators `Aᵢ(t)` of a fixed
time `t` and environment state; the statement is about any trace-preserving operator-sum
family, which is all the argument uses. `|j⟩⟨j|` is `Matrix.vecMulVec j (star j)`. -/
theorem eq_5_16_5_19 {s κ : Type} [Fintype s] [DecidableEq s] [Fintype κ]
    (A : κ → Matrix s s ℂ) (hA : ∑ i, (A i)ᴴ * A i = 1)
    (j : s → ℂ) (hj : star j ⬝ᵥ j = 1)
    (hinv : ∑ i, A i * Matrix.vecMulVec j (star j) * (A i)ᴴ = Matrix.vecMulVec j (star j)) :
    ∀ i, ∃ a : ℂ, A i *ᵥ j = a • j := by sorry

end BaconThesis.DFS
