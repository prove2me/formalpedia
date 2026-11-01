-- Prove2me | Theorems.Thm_BaconThesis_DFS_theorem_5_3_1
-- name    : BaconThesis.DFS.theorem_5_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T16:00:39.054153+00:00
-- url     : https://prove2.me/theorems/8fb0541b-3a26-4c80-b3a6-95aa00b38b75
-- title:
--   Theorem 5.3.1 — a subspace is decoherence-free iff every system operator $S_\alpha$ acts on it as a scalar
-- statement:
--   Let a system and an environment have finite-dimensional Hilbert spaces $\mathcal H_S$ and $\mathcal H_E$, and let them be coupled by a Hamiltonian
--   $$
--   H=\sum_{\alpha}S_\alpha\otimes B_\alpha
--   $$
--   with finitely many system operators $S_\alpha$ and **linearly independent** environment operators $B_\alpha$, $H$ Hermitian. Then a subspace $\mathcal S\subseteq\mathcal H_S$ is a decoherence-free subspace for $H$ (Definition 5.3.1: every pure state $|j\rangle\langle j|$ with $|j\rangle\in\mathcal S$ satisfies $\mathrm{Tr}_E[U(t)(|j\rangle\langle j|\otimes\rho_E)U^\dagger(t)]=|j\rangle\langle j|$ for every environment density operator $\rho_E$ and every $t\ge0$) **if and only if** there are complex numbers $c_\alpha$ with
--   $$
--   S_\alpha|j\rangle=c_\alpha|j\rangle\qquad\text{for every }\alpha\text{ and every }|j\rangle\in\mathcal S .
--   $$
--   The constants $c_\alpha$ are the same for all vectors of $\mathcal S$: a DFS is a degenerate common eigenspace of the system operators.
--
--   This is the basic criterion for decoherence-free subspaces: it replaces a condition on the evolution under every environment initial state by a finite set of linear-algebraic conditions on the coupling.
--
--   **Formalization Note** The coupling is the sum of Kronecker products on pairs (system index, environment index), system first; $U(t)=\exp[-iHt]$ and the partial trace is `WildeQIT.partialTraceRight`.
--
--   Differences from the source:
--   - generalization: B_α Hermitian, trace-orthonormal and a complete fixed basis (pp.68–69) → B_α only linearly independent; reason: Theorem 5.3.1's own hypothesis (§5.3, p.71) is linear independence; every expansion the book allows is covered
--   - reading: the time t in (5.12), not restricted in the text → every t ≥ 0; reason: the OSR evolution (2.8) runs forward from the initial time 0
--   - encoding: the OSR sum ∑_i A_i(t)|j⟩⟨j|A_i†(t) in (5.12) → Tr_E[U(t)(|j⟩⟨j| ⊗ ρ_E)U†(t)]; reason: the two are equal by (2.9)–(2.11) (milestone eq_2_9_2_11)
--   - encoding: "every pure state from this subspace", "∀ρ_E(0)" → every j ∈ S with ⟨j|j⟩ = 1, every density operator ρ_E on the environment; reason: Lean convention; same instances
--   - encoding: α = 0, …, A → a finite index type ι; reason: Lean convention; same instances
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, Theorem 5.3.1, eq. (5.13), p.72 (PDF p.89); Definition 5.3.1, eq. (5.12), p.72 (PDF p.89); eq. (5.1), p.68 (PDF p.85); §5.3, p.71 (PDF p.88)

import Mathlib
import Definitions.Def_BaconThesis_DFS_IsDFS

open scoped Matrix Kronecker

namespace BaconThesis.DFS

/-- **Theorem 5.3.1 (Decoherence-free subspace Hamiltonian criteria).**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1,
Theorem 5.3.1, eq. (5.13), p.72 (PDF p.89), for a system-environment coupling
`H = ∑_α S_α ⊗ B_α` (eq. (5.1), p.68) with linearly independent environment operators `B_α`
(§5.3, p.71): a subspace `S` is a DFS iff the system operators `S_α` act proportional to identity
on the subspace, `S_α|j⟩ = c_α|j⟩` for all `|j⟩ ∈ S`.

For finite system and environment index types, a finite family `S_α`, `B_α` with `B_α` linearly
independent and `H = ∑_α S_α ⊗ B_α` Hermitian, and every subspace `W` of the system space:
`W` is a decoherence-free subspace (Definition 5.3.1, `IsDFS`) if and only if there are complex
numbers `c_α`, one for each `α` and the same for every vector of `W`, with `S_α j = c_α j` for
all `j ∈ W`.

**Formalization Note.** Hilbert spaces are `s → ℂ`, `e → ℂ` with `Fintype s`, `Fintype e`; the
coupling is `∑_α Sα α ⊗ₖ Bα α` on `s × e` (system first). The book also takes the `B_α`
Hermitian, trace-orthonormal and complete; only linear independence (stated by the book for this
theorem) and Hermiticity of `H` are assumed. -/
theorem theorem_5_3_1 {s e ι : Type} [Fintype s] [DecidableEq s] [Fintype e] [DecidableEq e]
    [Fintype ι]
    (Sα : ι → Matrix s s ℂ) (Bα : ι → Matrix e e ℂ)
    (hH : (∑ α, Sα α ⊗ₖ Bα α).IsHermitian) (hB : LinearIndependent ℂ Bα)
    (W : Submodule ℂ (s → ℂ)) :
    IsDFS (∑ α, Sα α ⊗ₖ Bα α) W ↔ ∃ c : ι → ℂ, ∀ α, ∀ j ∈ W, Sα α *ᵥ j = c α • j := by sorry

end BaconThesis.DFS
