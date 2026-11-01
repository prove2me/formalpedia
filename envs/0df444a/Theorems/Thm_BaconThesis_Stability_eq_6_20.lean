-- Prove2me | Theorems.Thm_BaconThesis_Stability_eq_6_20
-- name    : BaconThesis.Stability.eq_6_20
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T16:00:00.657675+00:00
-- url     : https://prove2.me/theorems/565d2d4c-5f94-4af7-a29f-aaa8b69def7b
-- title:
--   Eq. (6.20) — the unperturbed evolution of a decoherence-free subsystem has vanishing decoherence rates to all orders
-- statement:
--   Let the system have the block basis $|K,\lambda,m\rangle$ and let $H_{SB}=\sum_\alpha S_\alpha\otimes B_\alpha$ be a Hermitian system-environment Hamiltonian whose system operators all have block form, $S_\alpha=\bigoplus_K I_{n_K}\otimes(S_{d_K})_\alpha$. Encode a unit vector $|j\rangle\in\mathbb C^{n_J}$ into the degeneracy of block $J$,
--   $$
--   \rho(0)=|j\rangle\langle j|\otimes\rho_{d_J}\quad(\text{on block }J),
--   $$
--   with $\rho_{d_J}$ a density matrix, and let the environment start in any density matrix $\rho_E$. Let $\rho(t)=\mathrm{Tr}_E[e^{-iH_{SB}t}(\rho(0)\otimes\rho_E)e^{iH_{SB}t}]$. Then for every order $p\ge1$
--   $$
--   \left(\frac1{\tau_p}\right)^{p}=\mathrm{Tr}\!\left[\Upsilon_J[\rho(0)]\;\Upsilon_J\big[\rho^{(p)}(0)\big]\right]=0 .
--   $$
--
--   This is the statement that the unperturbed evolution is decoherence-free on the degeneracy of block $J$, to all orders; it is the zeroth-order term of the stability expansion (6.26).
--
--   Differences from the source:
--   - reading: ⟨j|Υ_J[L^{ff(p)}(t)[ρ(0)]]|j⟩ = 0, the dissipative part of ρ^{(p)}(0) in the χ-matrix expansion (6.12)–(6.14), justified by "the unperturbed evolution is a DFS" → the whole unperturbed rate Tr[Υ_J[ρ(0)] Υ_J[ρ^{(p)}(0)]] (ε = 0) vanishes for every p ≥ 1; reason: the χ-matrix decomposition is a proof device and is not formalized; the unperturbed rate is the (6.18) term at ε = 0, which vanishes, plus the (6.20) term, so the two statements are equivalent given (6.18), and the vanishing of all unperturbed rates is what "the unperturbed evolution is a DFS" asserts
--   - generalization: the basis |J, λ, m⟩ of the irreps of the OSR algebra of the unperturbed evolution (Theorem 5.4.1, (5.31)) → any block decomposition Σ_K Fin n_K × Fin d_K in which every system operator S_α of H_SB has the block form ⊕_K I_{n_K} ⊗ (S_{d_K})_α; reason: the irrep basis of the OSR algebra is one such decomposition, and the argument uses only the block form (6.21); the Lean statement specializes to the book's
--   - encoding: a DFS-supporting system-environment Hamiltonian H_SB → H_SB = Σ_{α∈ι} S_α ⊗ B_α (finite index type ι), Hermitian; reason: every operator on a finite-dimensional S ⊗ E is a finite sum of products; the DFS condition is that the S_α lie in the block algebra
--   - encoding: ρ^{(p)}(0), the p-th time derivative of ρ(t) at t = 0 → entrywise iteratedDeriv p in the real time t at 0; reason: Lean convention; the entries of ρ(t) are smooth in t, so this is the ordinary derivative
--   - encoding: finite-dimensional system and environment in a fixed basis (Appendix A.3) → index types with Fintype; system index Σ_K Fin n_K × Fin d_K (0-based), system-environment index S × E; reason: Lean convention; same instances
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §6.2, eq. (6.20), p.91 (PDF p.108), with the rate of eq. (6.15), p.90 (PDF p.107)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_BaconThesis_Stability_IsBlockForm
import Definitions.Def_BaconThesis_Stability_encode
import Definitions.Def_BaconThesis_Stability_rate

open scoped Kronecker Matrix

namespace BaconThesis.Stability

/-- **Eq. (6.20): the unperturbed evolution is decoherence-free to all orders.**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1,
§6.2, eq. (6.20), p.91 (PDF p.108): "because the unperturbed evolution is a DFS,
`⟨j|Υ_J[L^{ff(p)}(t)[ρ(0)]]|j⟩ = 0`", with the rate of eq. (6.15), p.90 (PDF p.107).

Let the system have the block basis `|K, λ, m⟩` and let `H_SB = Σ_α S_α ⊗ B_α` be a Hermitian
system-environment Hamiltonian whose system operators all have the block form
`S_α = ⊕_K I_{n_K} ⊗ (S_{d_K})_α`. Encode a unit vector `|j⟩ ∈ ℂ^{n_J}` into the degeneracy of block
`J`, `ρ(0) = |j⟩⟨j| ⊗ ρ_{d_J}` with `ρ_{d_J}` a density matrix, and let the environment start in any
density matrix `ρ_E`. Then every decoherence rate of the unperturbed evolution vanishes:
`(1/τ_p)^p = Tr[Υ_J[ρ(0)] Υ_J[ρ^{(p)}(0)]] = 0` for every `p ≥ 1`.

**Formalization Note.** The book splits `ρ^{(p)}(0)` into the Hamiltonian part `S^{ff}` (whose
contribution vanishes by (6.18)) and the dissipative part `L^{ff}` of (6.14), and (6.20) is the
statement for the latter; the χ-matrix decomposition is not formalized, so the milestone states
the vanishing of the whole unperturbed rate. The system index type is
`Σ K : 𝒥, Fin (n K) × Fin (d K)`, the system-environment index `S × E` (system first), and
`|j⟩⟨j|` is `Matrix.vecMulVec j (star j)`. -/
theorem eq_6_20 {𝒥 E ι : Type} [Fintype 𝒥] [DecidableEq 𝒥] [Fintype E] [DecidableEq E]
    [Fintype ι] (n d : 𝒥 → ℕ)
    (S : ι → Matrix (Σ K : 𝒥, Fin (n K) × Fin (d K)) (Σ K : 𝒥, Fin (n K) × Fin (d K)) ℂ)
    (B : ι → Matrix E E ℂ) (hS : ∀ α, IsBlockForm n d (S α))
    (hH : (∑ α, S α ⊗ₖ B α).IsHermitian)
    (J : 𝒥) (j : Fin (n J) → ℂ) (hj : star j ⬝ᵥ j = 1)
    (ρd : Matrix (Fin (d J)) (Fin (d J)) ℂ) (hρd : WildeQIT.IsDensityOperator ρd)
    (ρE : Matrix E E ℂ) (hρE : WildeQIT.IsDensityOperator ρE)
    (p : ℕ) (hp : 1 ≤ p) :
    rate n d (∑ α, S α ⊗ₖ B α) (encode n d J (Matrix.vecMulVec j (star j)) ρd) ρE J p = 0 := by sorry

end BaconThesis.Stability
