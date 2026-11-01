-- Prove2me | Theorems.Thm_BaconThesis_Stability_eq_6_27
-- name    : BaconThesis.Stability.eq_6_27
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T16:00:04.253277+00:00
-- url     : https://prove2.me/theorems/c8bee6a0-1b57-40bf-8a15-32f848768042
-- title:
--   Eq. (6.27) — the stability of decoherence-free subsystems carries over to mixed encoded states
-- statement:
--   Same setting as eq. (6.26): $H_{SB}=\sum_\alpha S_\alpha\otimes B_\alpha$ Hermitian with every $S_\alpha$ of block form, $H'_I$ any Hermitian operator on the system-environment space, $\rho_{d_J}$ and $\rho_E$ density matrices, and the evolution under $H_{SB}+\epsilon H'_I$. Now encode a mixed state: let $|j_k\rangle\in\mathbb C^{n_J}$ be finitely many unit vectors and $p_k\ge0$ probabilities with $\sum_k p_k=1$, and put
--   $$
--   \rho(0)=\Big(\sum_k p_k\,|j_k\rangle\langle j_k|\Big)\otimes\rho_{d_J}\quad(\text{on block }J).
--   $$
--   Then for every $p\ge1$
--   $$
--   \left(\frac1{\tau_p}\right)^{p}=\mathrm{Tr}\!\left[\Upsilon_J[\rho(0)]\;\Upsilon_J\big[\rho_\epsilon^{(p)}(0)\big]\right]=O(\epsilon^2)\qquad(\epsilon\to0).
--   $$
--
--   The book observes that a mixed input evolves as the convex combination of the pure-state evolutions, so the perturbative analysis of eq. (6.26) carries over.
--
--   Differences from the source:
--   - reading: "the above perturbative analysis carries over to the initial mixed state case" (no formula printed for the mixed-state rate) → the rate (6.15) Tr[Υ_J[ρ(0)] Υ_J[ρ^{(p)}(0)]] of the mixed encoded state, with Υ_J[ρ(0)] = Σ_k p_k |j_k⟩⟨j_k|, is O(ε²); reason: (6.15) and (A.8) define the rate through ρ(0) itself, so this is the rate of the mixed input; it includes the cross terms ⟨j_l|Υ_J[ρ_k^{(p)}(0)]|j_l⟩ (k ≠ l) and so is not weaker than the per-component pure-state reading
--   - generalization: a mixed state Σ_j p_j |j⟩⟨j| →Σ_k p_k |j_k⟩⟨j_k| for any finite family of unit vectors |j_k⟩ (not required to be orthonormal) and probabilities p_k; reason: an orthonormal (spectral) family is a special case, so the Lean statement specializes to the book's
--   - generalization: the basis |J, λ, m⟩ of the irreps of the OSR algebra of the unperturbed evolution (Theorem 5.4.1, (5.31)) → any block decomposition Σ_K Fin n_K × Fin d_K in which every system operator S_α of H_SB has the block form ⊕_K I_{n_K} ⊗ (S_{d_K})_α; reason: the irrep basis of the OSR algebra is one such decomposition, and the argument uses only the block form (6.21); the Lean statement specializes to the book's
--   - encoding: a DFS-supporting system-environment Hamiltonian H_SB → H_SB = Σ_{α∈ι} S_α ⊗ B_α (finite index type ι), Hermitian; reason: every operator on a finite-dimensional S ⊗ E is a finite sum of products; the DFS condition is that the S_α lie in the block algebra
--   - encoding: ρ^{(p)}(0), the p-th time derivative of ρ(t) at t = 0 → entrywise iteratedDeriv p in the real time t at 0; reason: Lean convention; the entries of ρ(t) are smooth in t, so this is the ordinary derivative
--   - encoding: (1/τ_p)^p = 0 + O(ε²) → Asymptotics.IsBigO at 𝓝 (0 : ℝ) of the complex rate against ε ↦ ε²; reason: standard meaning of O(ε²) as ε → 0 (comparison of norms)
--   - encoding: finite-dimensional system and environment in a fixed basis (Appendix A.3) → index types with Fintype; system index Σ_K Fin n_K × Fin d_K (0-based), system-environment index S × E; reason: Lean convention; same instances
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §6.2, eq. (6.27) and the following sentence, p.92 (PDF p.109)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_BaconThesis_Stability_IsBlockForm
import Definitions.Def_BaconThesis_Stability_encode
import Definitions.Def_BaconThesis_Stability_rate

open scoped Kronecker Matrix
open Asymptotics Topology

namespace BaconThesis.Stability

/-- **Eq. (6.27): the stability result carries over to mixed encoded states.**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1,
§6.2, eq. (6.27) and the sentence after it, p.92 (PDF p.109): "a mixed state which evolves
according to the OSR can be thought of as a convex combination of the pure state evolutions
`ρ(t) = Σ_j p_j (Σ_i A_i(t)|j⟩⟨j|A_i†(t))`. This implies that the above perturbative analysis carries
over to the initial mixed state case."

Same setting as eq. (6.26) (`H_SB = Σ_α S_α ⊗ B_α` Hermitian with every `S_α` of block form, `H'_I`
any Hermitian operator, `ρ_{d_J}` and `ρ_E` density matrices), but the encoded information is a
mixed state `Σ_k p_k |j_k⟩⟨j_k|` (finitely many unit vectors `|j_k⟩ ∈ ℂ^{n_J}`, probabilities
`p_k ≥ 0` with `Σ_k p_k = 1`): `ρ(0) = (Σ_k p_k |j_k⟩⟨j_k|) ⊗ ρ_{d_J}` on block `J`. For every `p ≥ 1`
the rate `(1/τ_p)^p = Tr[Υ_J[ρ(0)] Υ_J[ρ^{(p)}(0)]]` of the evolution under `H_SB + ε H'_I` is `O(ε²)`
as `ε → 0`.

**Formalization Note.** As in eq. (6.26): `O(ε²)` is `Asymptotics.IsBigO` at `𝓝 (0 : ℝ)` against
`ε ↦ ε²`; the rate is defined with `Υ_J[ρ(0)]`, as in (6.15) and (A.8). The pure states are indexed
by any finite type `κ` (the book's index `j`). -/
theorem eq_6_27 {𝒥 E ι κ : Type} [Fintype 𝒥] [DecidableEq 𝒥] [Fintype E] [DecidableEq E]
    [Fintype ι] [Fintype κ] (n d : 𝒥 → ℕ)
    (S : ι → Matrix (Σ K : 𝒥, Fin (n K) × Fin (d K)) (Σ K : 𝒥, Fin (n K) × Fin (d K)) ℂ)
    (B : ι → Matrix E E ℂ) (hS : ∀ α, IsBlockForm n d (S α))
    (hH : (∑ α, S α ⊗ₖ B α).IsHermitian)
    (HI : Matrix ((Σ K : 𝒥, Fin (n K) × Fin (d K)) × E) ((Σ K : 𝒥, Fin (n K) × Fin (d K)) × E) ℂ)
    (hHI : HI.IsHermitian)
    (J : 𝒥) (q : κ → ℝ) (hq : ∀ k, 0 ≤ q k) (hq1 : ∑ k, q k = 1)
    (j : κ → Fin (n J) → ℂ) (hj : ∀ k, star (j k) ⬝ᵥ j k = 1)
    (ρd : Matrix (Fin (d J)) (Fin (d J)) ℂ) (hρd : WildeQIT.IsDensityOperator ρd)
    (ρE : Matrix E E ℂ) (hρE : WildeQIT.IsDensityOperator ρE)
    (p : ℕ) (hp : 1 ≤ p) :
    (fun ε : ℝ => rate n d ((∑ α, S α ⊗ₖ B α) + (ε : ℂ) • HI)
        (encode n d J (∑ k, (q k : ℂ) • Matrix.vecMulVec (j k) (star (j k))) ρd) ρE J p)
      =O[𝓝 0] (fun ε : ℝ => ε ^ 2) := by sorry

end BaconThesis.Stability
