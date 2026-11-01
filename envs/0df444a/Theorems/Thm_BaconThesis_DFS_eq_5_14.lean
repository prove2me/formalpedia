-- Prove2me | Theorems.Thm_BaconThesis_DFS_eq_5_14
-- name    : BaconThesis.DFS.eq_5_14
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:59:45.285997+00:00
-- url     : https://prove2.me/theorems/01bf36b9-4dda-4f84-9593-df18a3fe117f
-- title:
--   Eq. (5.14) — if every $S_\alpha$ is a scalar $c_\alpha$ on $\mathcal S$, every OSR operator is a scalar on $\mathcal S$
-- statement:
--   Let $H=\sum_\alpha S_\alpha\otimes B_\alpha$ on $\mathcal H_S\otimes\mathcal H_E$ (finite dimensional, finitely many terms) and let $\mathcal S\subseteq\mathcal H_S$ be a subspace on which every system operator acts as a scalar: there are $c_\alpha\in\mathbb C$ with
--   $$
--   S_\alpha|j\rangle=c_\alpha|j\rangle\qquad\text{for all }\alpha\text{ and all }|j\rangle\in\mathcal S .
--   $$
--   Then for every time $t$ and all environment vectors $\varphi,\psi$, the OSR operator $\langle\varphi|U(t)|\psi\rangle$ acts on $\mathcal S$ as one scalar:
--   $$
--   \langle\varphi|U(t)|\psi\rangle\,|j\rangle=c(t)\,|j\rangle\quad\text{for all }|j\rangle\in\mathcal S,
--   \qquad c(t)=\Big\langle\varphi\Big|\exp\Big[-it\sum_\alpha c_\alpha B_\alpha\Big]\Big|\psi\Big\rangle .
--   $$
--
--   This is the first half of the sufficiency proof of Theorem 5.3.1: the constant $c_i(t)$ of each OSR operator $A_i(t)$ depends on the system only through the $c_\alpha$.
--
--   **Formalization Note** The book's OSR operators are the case $\varphi=|\mu\rangle$, $\psi=\sqrt{p_\nu}|\nu\rangle$. The exponential is the matrix exponential on the environment.
--
--   Differences from the source:
--   - generalization: "c_i is some complex constant which is a complex combination of the c_α's" → the explicit constant ⟨φ|exp(−it ∑_α c_α B_α)|ψ⟩; reason: names the constant, which depends on the system only through the c_α; it implies the book's existence claim
--   - generalization: the OSR operators A_i(t) → ⟨φ|U(t)|ψ⟩ for all environment vectors φ, ψ; reason: the book's operators are the case φ = |µ⟩, ψ = √p_ν|ν⟩
--   - generalization: B_α Hermitian, linearly independent, trace-orthonormal, H a Hamiltonian, t the evolution time → no condition on the B_α or on H, every real t; reason: the book's setting is among those covered
--   - encoding: α = 0, …, A → a finite index type ι; reason: Lean convention; same instances
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, proof of Theorem 5.3.1, eq. (5.14), p.72 (PDF p.89)

import Mathlib
import Definitions.Def_BaconThesis_DFS_osrOp

open scoped Matrix Kronecker

namespace BaconThesis.DFS

/-- **Sufficiency step, eq. (5.14): every OSR operator acts as a scalar on the subspace.**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1,
proof of Theorem 5.3.1, eq. (5.14), p.72 (PDF p.89): if `S_α|j⟩ = c_α|j⟩` for all `|j⟩ ∈ S`, then
`Aᵢ(t)|j⟩ = cᵢ(t)|j⟩`, where `cᵢ` is some complex constant which is a complex combination of the
`c_α`'s.

Let `H = ∑_α S_α ⊗ B_α` and let `W` be a subspace with `S_α j = c_α j` for every `α` and every
`j ∈ W`. Then for every time `t` and all environment vectors `φ`, `ψ`, the OSR operator
`⟨φ|U(t)|ψ⟩` acts on `W` as the scalar `⟨φ|exp(−it ∑_α c_α B_α)|ψ⟩`, the same for every `j ∈ W`.

**Formalization Note.** The scalar `cᵢ(t)` of the book is given explicitly; it depends only on
the `c_α`, the `B_α`, `t`, `φ` and `ψ`. The book's OSR operators are
`A_{(µ,ν)}(t) = osrOp H t |µ⟩ (√p_ν|ν⟩)`. No condition is placed on the `B_α` or on `H`, and
`t` is any real number. -/
theorem eq_5_14 {s e ι : Type} [Fintype s] [DecidableEq s] [Fintype e] [DecidableEq e]
    [Fintype ι]
    (Sα : ι → Matrix s s ℂ) (Bα : ι → Matrix e e ℂ) (W : Submodule ℂ (s → ℂ))
    (c : ι → ℂ) (hc : ∀ α, ∀ j ∈ W, Sα α *ᵥ j = c α • j) (t : ℝ) (φ ψ : e → ℂ) :
    ∀ j ∈ W, osrOp (∑ α, Sα α ⊗ₖ Bα α) t φ ψ *ᵥ j =
      (star φ ⬝ᵥ (evolOp (∑ α, c α • Bα α) t *ᵥ ψ)) • j := by sorry

end BaconThesis.DFS
