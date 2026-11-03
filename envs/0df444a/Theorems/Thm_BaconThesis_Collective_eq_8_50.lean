-- Prove2me | Theorems.Thm_BaconThesis_Collective_eq_8_50
-- name    : BaconThesis.Collective.eq_8_50
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:14:23.25519+00:00
-- url     : https://prove2.me/theorems/a7b8d13a-92ce-4ab8-a76b-4ad610495743
-- title:
--   Eq. (8.50) — $S_-|J,\lambda,m\rangle=\sqrt{(J+m)(J-m+1)}\,|J,\lambda,m-1\rangle$ and $S_+S_-|J,\lambda,m\rangle=(J+m)(J-m+1)|J,\lambda,m\rangle$
-- statement:
--   Let $W$ be a unitary from the $n$-qubit space onto $\bigoplus_J\mathbb C^{n_J}\otimes\mathbb C^{2J+1}$ that brings the collective operators to the form (8.43),
--   $$
--   W S_\alpha W^\dagger=\bigoplus_J I_{n_J}\otimes S_\alpha(2J+1)\qquad(\alpha=x,y,z),
--   $$
--   and let $|J,\lambda,m\rangle=W^\dagger e_{J,\lambda,m}$ be the corresponding basis of §8.6 ($\lambda$ the degeneracy index, $-J\le m\le J$). Then, with $S_\pm=S_x\pm iS_y$, for every basis vector
--   $$
--   S_-|J,\lambda,m\rangle=\sqrt{(J+m)(J-m+1)}\;|J,\lambda,m-1\rangle,\qquad S_+S_-|J,\lambda,m\rangle=(J+m)(J-m+1)\,|J,\lambda,m\rangle,
--   $$
--   where $|J,\lambda,-J-1\rangle$ is read as $0$ (the coefficient vanishes at $m=-J$).
--
--   These are the actions of the collective amplitude damping Lindblad operator $S_-$ and Hamiltonian $S_+S_-$; the DF subspace analysis of §8.7 is read off from them.
--
--   Differences from the source:
--   - reading: the |J, λ, m⟩ basis from Section 8.6 → the columns of W† for any unitary W with W S_α W† = ⊕_J I ⊗ S_α(2J+1), α = x, y, z; reason: §8.6 defines the basis as one on which S_α acts as |J, λ⟩ ⊗ S_α(2J+1)|m⟩ (p.118)
--   - generalization: the basis |J, λ, m⟩ → every basis of that form; reason: the book's basis is one such W†
--   - encoding: J, m (half-integers), |J, λ, m − 1⟩ → J = n/2 − r and m = J − k with r ∈ Fin (⌊n/2⌋+1), k ∈ Fin (n − 2r + 1); m − 1 is index k + 1, and 0 when m = −J; reason: avoids half-integer indices; at m = −J the book's coefficient is 0
--   - generalization: n qubits, n ≥ 1 (the book starts at n = 1, (8.44)) → every n ∈ ℕ, including n = 0; reason: at n = 0 the space is one-dimensional and every collective operator is 0, where the statement also holds; for n ≥ 1 it is the book's statement
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, (8.50), §8.7, p.121 (PDF p.138)

import Mathlib
import Definitions.Def_BBPSSW_Distill_pauli
import Definitions.Def_BaconThesis_Collective_onQubit
import Definitions.Def_BaconThesis_Collective_collS
import Definitions.Def_BaconThesis_Collective_collPlus
import Definitions.Def_BaconThesis_Collective_collMinus
import Definitions.Def_BaconThesis_Collective_spinRep
import Definitions.Def_BaconThesis_Collective_BlockIdx
import Definitions.Def_BaconThesis_Collective_blockOp

open scoped Matrix

namespace BaconThesis.Collective

/-- **(8.50): the action of `S_−^[n]` and `S_+^[n] S_−^[n]` on the basis `|J, λ, m⟩`.**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1, §8.7, (8.50), p.121 (PDF p.138): "Using the `|J, λ, m⟩` basis from Section 8.6 the action
of both of these operators can be evaluated:
`S_−^[n]|J_n, λ, m⟩ = √((J_n + m)(J_n − m + 1)) |J_n, λ, m − 1⟩`,
`S_+^[n] S_−^[n]|J_n, λ, m⟩ = (J_n + m)(J_n − m + 1)|J_n, λ, m⟩`."

Let `W` be any unitary from `n` qubits onto `⊕_J ℂ^(m_J) ⊗ ℂ^(2J+1)` that puts the collective
operators in the form (8.43), `W S_α W† = ⊕_J I ⊗ S_α(2J+1)` for `α = x, y, z`. Let
`|J, λ, m⟩ = W† e_(r, λ, k)` (with `J = n/2 − r`, `m = J − k`), the basis of §8.6. Then for every
such basis vector

* `S_−^[n] |J, λ, m⟩ = √((J + m)(J − m + 1)) |J, λ, m − 1⟩`, where `|J, λ, m − 1⟩ := 0` when
  `m = −J` (then the coefficient is `0` as well), and
* `S_+^[n] S_−^[n] |J, λ, m⟩ = (J + m)(J − m + 1) |J, λ, m⟩`.

**Formalization Note.** `J = n/2 − r` and `m = J − k` are encoded by `r ∈ Fin (⌊n/2⌋+1)` and
`k ∈ Fin (n − 2r + 1)` (see `BlockIdx`); `m − 1` is index `k + 1`. The statement holds for every
basis of the form (8.43), not only one. `S_± = S_x ± iS_y` per the book's `σ_± = σ_x ± iσ_y`
and (8.30). The vector `|J, λ, m⟩` is the column `(r, λ, k)` of `W†`. -/
theorem eq_8_50 (n : ℕ) (m : Fin (n / 2 + 1) → ℕ) (W : Matrix (BlockIdx n m) (Fin n → Fin 2) ℂ)
    (hW : Wᴴ * W = 1) (hW' : W * Wᴴ = 1)
    (hS : ∀ α : BBPSSW.Distill.Axis, W * collS n α * Wᴴ = blockOp n m (fun r => spinRep (n - 2 * r.val) α))
    (r : Fin (n / 2 + 1)) (lam : Fin (m r)) (k : Fin (n - 2 * r.val + 1)) :
    let J : ℝ := (n : ℝ) / 2 - (r.val : ℝ)
    let mz : ℝ := J - (k.val : ℝ)
    let ket : BlockIdx n m → (Fin n → Fin 2) → ℂ := fun i x => star (W i x)
    (collMinus n *ᵥ ket ⟨r, lam, k⟩ =
        ((Real.sqrt ((J + mz) * (J - mz + 1)) : ℝ) : ℂ) •
          (if h : k.val + 1 < n - 2 * r.val + 1 then ket ⟨r, lam, ⟨k.val + 1, h⟩⟩ else 0)) ∧
      ((collPlus n * collMinus n) *ᵥ ket ⟨r, lam, k⟩ =
        (((J + mz) * (J - mz + 1) : ℝ) : ℂ) • ket ⟨r, lam, k⟩) := by sorry

end BaconThesis.Collective
