-- Prove2me | Theorems.Thm_BaconThesis_DFS_eq_2_12
-- name    : BaconThesis.DFS.eq_2_12
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:59:26.35127+00:00
-- url     : https://prove2.me/theorems/53a91ff2-9d57-4205-9e32-9a1ef86a5485
-- title:
--   Eq. (2.12) — OSR normalization $\sum_i A_i^\dagger(t)A_i(t)=I$
-- statement:
--   Let $H$ be a Hermitian operator on $\mathcal H_S\otimes\mathcal H_E$ (finite dimensional), so that $U(t)=\exp[-iHt]$ is unitary. Let $\{\varphi_m\}$ be a finite family of environment vectors with $\sum_m|\varphi_m\rangle\langle\varphi_m|=I_E$, and $\{\psi_\nu\}$ a finite family of environment vectors with $\sum_\nu\langle\psi_\nu|\psi_\nu\rangle=1$. Then for every time $t$ the OSR operators $A_{m,\nu}(t)=\langle\varphi_m|U(t)|\psi_\nu\rangle$ satisfy
--   $$
--   \sum_{m,\nu}A_{m,\nu}^\dagger(t)\,A_{m,\nu}(t)=I_S .
--   $$
--
--   In the thesis $\varphi_m=|\mu\rangle$ is an orthonormal basis and $\psi_\nu=\sqrt{p_\nu}|\nu\rangle$ with $\rho_E(0)=\sum_\nu p_\nu|\nu\rangle\langle\nu|$, so $\sum_\nu\langle\psi_\nu|\psi_\nu\rangle=\sum_\nu p_\nu=1$. Together with (2.10) this normalization makes the operator-sum representation trace preserving; it is the identity used in the proofs of both directions of Theorem 5.3.1.
--
--   **Formalization Note** The joint space is indexed by pairs, system first.
--
--   Differences from the source:
--   - generalization: an orthonormal basis |µ⟩ of the environment → any finite family φ_m with ∑_m |φ_m⟩⟨φ_m| = I; reason: orthonormal bases resolve the identity, so the book's case is included
--   - generalization: ψ_ν = √p_ν|ν⟩ with |ν⟩ orthonormal and ∑_ν p_ν = 1 → any finite family ψ_ν with ∑_ν ⟨ψ_ν|ψ_ν⟩ = 1; reason: the book's family has ∑_ν ⟨ψ_ν|ψ_ν⟩ = ∑_ν p_ν = 1
--   - encoding: U(t) is unitary → H is Hermitian (U(t) = exp(−itH)); reason: a Hamiltonian is Hermitian, which is what makes U(t) unitary in the book; same instances
--   - generalization: the evolution time t → every real t; reason: U(t) is unitary for every real t when H is Hermitian; includes every t ≥ 0
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §2.2.1, eq. (2.12), p.16 (PDF p.33)

import Mathlib
import Definitions.Def_BaconThesis_DFS_osrOp

open scoped Matrix

namespace BaconThesis.DFS

/-- **OSR normalization, eq. (2.12).**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1,
§2.2.1, eq. (2.12), p.16 (PDF p.33): "The requirement that U(t) is unitary implies that
`∑_{i=(µ,ν)} Aᵢ†(t)Aᵢ(t) = I`."

For a Hermitian joint Hamiltonian `H` (so that `U(t) = exp(−itH)` is unitary), every time `t`,
every family `φ_m` with `∑_m |φ_m⟩⟨φ_m| = I` and every family `ψ_ν` with
`∑_ν ⟨ψ_ν|ψ_ν⟩ = 1`, the OSR operators `A_{m,ν}(t) = ⟨φ_m|U(t)|ψ_ν⟩` satisfy
`∑_{m,ν} A_{m,ν}(t)† A_{m,ν}(t) = I`.

**Formalization Note.** The book's case is `φ_m = |µ⟩` an orthonormal basis and
`ψ_ν = √p_ν|ν⟩` with `ρ_E(0) = ∑_ν p_ν|ν⟩⟨ν|` the spectral decomposition, where
`∑_ν ⟨ψ_ν|ψ_ν⟩ = ∑_ν p_ν = 1`. -/
theorem eq_2_12 {s e κ μ : Type} [Fintype s] [DecidableEq s] [Fintype e] [DecidableEq e]
    [Fintype κ] [Fintype μ]
    (H : Matrix (s × e) (s × e) ℂ) (hH : H.IsHermitian) (t : ℝ)
    (φ : μ → e → ℂ) (hφ : ∑ m, Matrix.vecMulVec (φ m) (star (φ m)) = 1)
    (ψ : κ → e → ℂ) (hψ : ∑ ν, star (ψ ν) ⬝ᵥ ψ ν = 1) :
    ∑ m, ∑ ν, (osrOp H t (φ m) (ψ ν))ᴴ * osrOp H t (φ m) (ψ ν) = 1 := by sorry

end BaconThesis.DFS
