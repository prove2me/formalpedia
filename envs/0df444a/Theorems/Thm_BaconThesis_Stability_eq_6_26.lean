-- Prove2me | Theorems.Thm_BaconThesis_Stability_eq_6_26
-- name    : BaconThesis.Stability.eq_6_26
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T16:00:15.064786+00:00
-- url     : https://prove2.me/theorems/9fd72abc-b102-46bf-97a6-ffd4eda0b19b
-- title:
--   Eq. (6.26) — decoherence-free subsystems are stable: every decoherence rate is $0+O(\epsilon^2)$
-- statement:
--   Let the system have the block basis $|K,\lambda,m\rangle$ ($K\in\mathcal J$, $\lambda\le n_K$, $m\le d_K$). Let $H_{SB}=\sum_\alpha S_\alpha\otimes B_\alpha$ be a Hermitian system-environment Hamiltonian whose system operators all have block form, $S_\alpha=\bigoplus_K I_{n_K}\otimes(S_{d_K})_\alpha$, and let $H'_I$ be any Hermitian operator on the system-environment space. For $\epsilon\in\mathbb R$ consider the perturbed Hamiltonian
--   $$
--   H'_{SB}=H_{SB}+\epsilon H'_I .
--   $$
--   Encode a unit vector $|j\rangle\in\mathbb C^{n_J}$ into the degeneracy of block $J$, $\rho(0)=|j\rangle\langle j|\otimes\rho_{d_J}$ with $\rho_{d_J}$ a density matrix, let the environment start in any density matrix $\rho_E$, and let $\rho_\epsilon(t)=\mathrm{Tr}_E[e^{-iH'_{SB}t}(\rho(0)\otimes\rho_E)e^{iH'_{SB}t}]$. Then for every order $p\ge1$ the $p$-th decoherence rate satisfies
--   $$
--   \left(\frac1{\tau_p}\right)^{p}=\mathrm{Tr}\!\left[\Upsilon_J[\rho(0)]\;\Upsilon_J\big[\rho_\epsilon^{(p)}(0)\big]\right]=0+O(\epsilon^2)\qquad(\epsilon\to0).
--   $$
--
--   So a perturbing interaction of strength $\epsilon$ degrades a decoherence-free subsystem only at second order, however strong the unperturbed coupling is: the decoherence rates have no term of order $\epsilon^0$ or $\epsilon^1$.
--
--   Differences from the source:
--   - generalization: the basis |J, λ, m⟩ of the irreps of the OSR algebra of the unperturbed evolution (Theorem 5.4.1, (5.31)) → any block decomposition Σ_K Fin n_K × Fin d_K in which every system operator S_α of H_SB has the block form ⊕_K I_{n_K} ⊗ (S_{d_K})_α; reason: the irrep basis of the OSR algebra is one such decomposition, and the argument uses only the block form (6.21); the Lean statement specializes to the book's
--   - encoding: a DFS-supporting system-environment Hamiltonian H_SB → H_SB = Σ_{α∈ι} S_α ⊗ B_α (finite index type ι), Hermitian; reason: every operator on a finite-dimensional S ⊗ E is a finite sum of products; the DFS condition is that the S_α lie in the block algebra
--   - encoding: ρ^{(p)}(0), the p-th time derivative of ρ(t) at t = 0 → entrywise iteratedDeriv p in the real time t at 0; reason: Lean convention; the entries of ρ(t) are smooth in t, so this is the ordinary derivative
--   - encoding: (1/τ_p)^p = 0 + O(ε²) → Asymptotics.IsBigO at 𝓝 (0 : ℝ) of the complex rate against ε ↦ ε²; reason: standard meaning of O(ε²) as ε → 0 (comparison of norms)
--   - encoding: finite-dimensional system and environment in a fixed basis (Appendix A.3) → index types with Fintype; system index Σ_K Fin n_K × Fin d_K (0-based), system-environment index S × E; reason: Lean convention; same instances
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §6.2, eq. (6.26), p.91 (PDF p.108), with eq. (6.4), p.88 (PDF p.105) and eq. (6.15), p.90 (PDF p.107)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_BaconThesis_Stability_IsBlockForm
import Definitions.Def_BaconThesis_Stability_encode
import Definitions.Def_BaconThesis_Stability_rate

open scoped Kronecker Matrix
open Asymptotics Topology

namespace BaconThesis.Stability

/-- **Eq. (6.26): decoherence-free subsystems are stable — every decoherence rate is `0 + O(ε²)`.**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1,
§6.2, eq. (6.26), p.91 (PDF p.108): "to first order in `ε`, the decoherence rates of a DFS on the
OSR for a perturbing interaction of strength `ε` vanishes `(1/τ_p)^p = 0 + O(ε²)`", with the
perturbed Hamiltonian `H'_SB = H_SB + ε H'_I` of eq. (6.4), p.88 (PDF p.105), and the encoding and
rate of eq. (6.15), p.90 (PDF p.107).

Let the system have the block basis `|K, λ, m⟩` (`K ∈ 𝒥`, `λ < n_K`, `m < d_K`), let
`H_SB = Σ_α S_α ⊗ B_α` be a Hermitian system-environment Hamiltonian whose system operators all
have the block form `S_α = ⊕_K I_{n_K} ⊗ (S_{d_K})_α`, and let `H'_I` be any Hermitian operator on
the system-environment space. Encode a unit vector `|j⟩ ∈ ℂ^{n_J}` into the degeneracy of block `J`,
`ρ(0) = |j⟩⟨j| ⊗ ρ_{d_J}` with `ρ_{d_J}` a density matrix, and let the environment start in any
density matrix `ρ_E`. For every order `p ≥ 1`, the `p`-th decoherence rate
`(1/τ_p)^p = Tr[Υ_J[ρ(0)] Υ_J[ρ^{(p)}(0)]]` of the evolution under `H_SB + ε H'_I` is `O(ε²)` as
`ε → 0`.

**Formalization Note.** `O(ε²)` is `Asymptotics.IsBigO` at `𝓝 (0 : ℝ)` of the complex-valued rate
against the real function `ε ↦ ε²` (comparison of norms). The block structure is given as data
rather than derived from the OSR algebra by Theorem 5.4.1; the hypothesis is that every `S_α` has
the block form. The system index type is `Σ K : 𝒥, Fin (n K) × Fin (d K)`, the system-environment
index `S × E` (system first), `|j⟩⟨j|` is `Matrix.vecMulVec j (star j)`, and the strength `ε` is any
real number. -/
theorem eq_6_26 {𝒥 E ι : Type} [Fintype 𝒥] [DecidableEq 𝒥] [Fintype E] [DecidableEq E]
    [Fintype ι] (n d : 𝒥 → ℕ)
    (S : ι → Matrix (Σ K : 𝒥, Fin (n K) × Fin (d K)) (Σ K : 𝒥, Fin (n K) × Fin (d K)) ℂ)
    (B : ι → Matrix E E ℂ) (hS : ∀ α, IsBlockForm n d (S α))
    (hH : (∑ α, S α ⊗ₖ B α).IsHermitian)
    (HI : Matrix ((Σ K : 𝒥, Fin (n K) × Fin (d K)) × E) ((Σ K : 𝒥, Fin (n K) × Fin (d K)) × E) ℂ)
    (hHI : HI.IsHermitian)
    (J : 𝒥) (j : Fin (n J) → ℂ) (hj : star j ⬝ᵥ j = 1)
    (ρd : Matrix (Fin (d J)) (Fin (d J)) ℂ) (hρd : WildeQIT.IsDensityOperator ρd)
    (ρE : Matrix E E ℂ) (hρE : WildeQIT.IsDensityOperator ρE)
    (p : ℕ) (hp : 1 ≤ p) :
    (fun ε : ℝ => rate n d ((∑ α, S α ⊗ₖ B α) + (ε : ℂ) • HI)
        (encode n d J (Matrix.vecMulVec j (star j)) ρd) ρE J p) =O[𝓝 0] (fun ε : ℝ => ε ^ 2) := by sorry

end BaconThesis.Stability
