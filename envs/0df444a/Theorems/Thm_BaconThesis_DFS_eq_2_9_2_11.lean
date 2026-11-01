-- Prove2me | Theorems.Thm_BaconThesis_DFS_eq_2_9_2_11
-- name    : BaconThesis.DFS.eq_2_9_2_11
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:59:40.007916+00:00
-- url     : https://prove2.me/theorems/85716c01-9f4e-4244-a814-db0444d77874
-- title:
--   Eqs. (2.9)–(2.11) — the reduced evolution in operator-sum form $\sum_i A_i(t)\rho A_i^\dagger(t)$
-- statement:
--   Let $\mathcal H_S=\mathbb C^{s}$ and $\mathcal H_E=\mathbb C^{e}$ be finite dimensional, let $H$ be an operator on $\mathcal H_S\otimes\mathcal H_E$ and $U(t)=\exp[-iHt]$. Let $\{\varphi_m\}$ be a finite family of environment vectors resolving the identity, $\sum_m|\varphi_m\rangle\langle\varphi_m|=I_E$, and let the environment state be written as $\rho_E=\sum_\nu|\psi_\nu\rangle\langle\psi_\nu|$ for a finite family $\{\psi_\nu\}$. Then for every time $t$ and every system operator $\rho$,
--   $$
--   \mathrm{Tr}_E\!\left[\,U(t)\,(\rho\otimes\rho_E)\,U^\dagger(t)\,\right]=\sum_{m,\nu}A_{m,\nu}(t)\,\rho\,A_{m,\nu}^\dagger(t),
--   \qquad A_{m,\nu}(t)=\langle\varphi_m|U(t)|\psi_\nu\rangle .
--   $$
--
--   In the thesis $\{\varphi_m\}=\{|\mu\rangle\}$ is an orthonormal basis and $\psi_\nu=\sqrt{p_\nu}|\nu\rangle$ comes from the spectral decomposition $\rho_E(0)=\sum_\nu p_\nu|\nu\rangle\langle\nu|$, which gives the OSR operators $A_{(\mu,\nu)}(t)=\sqrt{p_\nu}\langle\mu|U(t)|\nu\rangle$ of (2.11). This identity is what lets the definition of a decoherence-free subspace be stated either with the partial trace or with OSR operators.
--
--   **Formalization Note** The joint space is indexed by pairs, system first; the partial trace is `WildeQIT.partialTraceRight` over the environment.
--
--   Differences from the source:
--   - generalization: an orthonormal basis |µ⟩ of the environment → any finite family φ_m with ∑_m |φ_m⟩⟨φ_m| = I; reason: orthonormal bases resolve the identity, so the book's case is included
--   - generalization: ψ_ν = √p_ν|ν⟩ from the spectral decomposition of a state ρ_E(0) → any finite family ψ_ν, with ρ_E = ∑_ν |ψ_ν⟩⟨ψ_ν|; reason: the book's decomposition is one such family
--   - generalization: the initial system state ρ_S(0), a joint Hamiltonian H and the evolution time t → any system matrix ρ, any joint matrix H and any real t; reason: both sides are defined for all of them; the book's case is included
--   - encoding: Tr_E[U(t)ρ_S(0) ⊗ ρ_E(0)U†(t)] → WildeQIT.partialTraceRight of a Kronecker product on s × e (system first); reason: Lean convention; same quantity
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §2.2.1, eqs. (2.8)–(2.11), p.16 (PDF p.33)

import Mathlib
import Definitions.Def_BaconThesis_DFS_osrEvolve
import Definitions.Def_BaconThesis_DFS_osrOp

open scoped Matrix

namespace BaconThesis.DFS

/-- **The reduced evolution in operator-sum form, eqs. (2.9)–(2.11).**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1,
§2.2.1, eqs. (2.9)–(2.11), p.16 (PDF p.33): with the spectral decomposition
`ρ_E(0) = ∑_ν p_ν |ν⟩⟨ν|` and an orthonormal basis `|µ⟩` of the environment,
`ρ_S(t) = ∑_{µ,ν} ⟨µ|U(t)ρ_S(0)p_ν|ν⟩⟨ν|U†(t)|µ⟩ = ∑ᵢ Aᵢ(t)ρ_S(0)Aᵢ†(t)` with
`A_{i=(µ,ν)}(t) = √p_ν⟨µ|U(t)|ν⟩`.

If the environment state is `ρE = ∑_ν |ψ_ν⟩⟨ψ_ν|` and the vectors `φ_m` satisfy the completeness
relation `∑_m |φ_m⟩⟨φ_m| = I`, then for every joint `H`, time `t` and system operator `ρ`,
`Tr_E[U(t)(ρ ⊗ ρE)U(t)†] = ∑_{m,ν} A_{m,ν}(t) ρ A_{m,ν}(t)†` with
`A_{m,ν}(t) = ⟨φ_m|U(t)|ψ_ν⟩` (`osrOp`).

**Formalization Note.** The book's case is `φ_m = |µ⟩` an orthonormal basis and
`ψ_ν = √p_ν |ν⟩` from the spectral decomposition; the statement allows any decomposition of
`ρE` into rank-one terms and any family `φ` resolving the identity. `|x⟩⟨y|` is
`Matrix.vecMulVec x (star y)`. -/
theorem eq_2_9_2_11 {s e κ μ : Type} [Fintype s] [DecidableEq s] [Fintype e] [DecidableEq e]
    [Fintype κ] [Fintype μ]
    (H : Matrix (s × e) (s × e) ℂ) (t : ℝ)
    (φ : μ → e → ℂ) (hφ : ∑ m, Matrix.vecMulVec (φ m) (star (φ m)) = 1)
    (ψ : κ → e → ℂ) (ρ : Matrix s s ℂ) :
    osrEvolve H (∑ ν, Matrix.vecMulVec (ψ ν) (star (ψ ν))) t ρ =
      ∑ m, ∑ ν, osrOp H t (φ m) (ψ ν) * ρ * (osrOp H t (φ m) (ψ ν))ᴴ := by sorry

end BaconThesis.DFS
