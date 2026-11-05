-- Prove2me | Theorems.Thm_FermionModewise_main_result
-- name    : FermionModewise.main_result
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:34:05.788906+00:00
-- url     : https://prove2.me/theorems/d793eb4c-fe7e-4c81-bc7f-ab5cfa735883
-- title:
--   Main result: under any bipartition of modes, a pure fermion Gaussian state is a product of two-mode squeezed pairs and vacuum modes in locally transformed modes
-- statement:
--   Let $N$ fermion modes $b$, satisfying the canonical anticommutation relations on a finite-dimensional space, be partitioned into two arbitrary sets $A=\{A_1,\dots,A_m\}$ and $B=\{B_1,\dots,B_n\}$, $n=N-m$, and let $|\psi\rangle_{AB}$ be any pure fermion Gaussian state of the modes. Then there exist
--   1. new sets of modes $\tilde A=\{\tilde A_1,\dots,\tilde A_m\}$ and $\tilde B=\{\tilde B_1,\dots,\tilde B_n\}$, obtained from $A$ and from $B$ respectively by **local** fermion canonical transformations;
--   2. a number $s\le\min(m,n)$ and a pairing of $s$ modes of $\tilde A$ with $s$ modes of $\tilde B$, written $(\tilde A_k,\tilde B_k)$, $k\le s$;
--   3. angles $\theta_k\in(0,\pi/4]$;
--   4. a unit vector $|0\rangle$ annihilated by every mode of $\tilde A$ and of $\tilde B$,
--
--   such that
--   $$|\psi\rangle_{AB}=\prod_{k=1}^s\big(\cos\theta_k-\sin\theta_k\,\tilde A_k^\dagger\tilde B_k^\dagger\big)|0\rangle .$$
--   That is, $|\psi\rangle_{AB}=|\tilde\psi_1\rangle_{\tilde A_1\tilde B_1}\cdots|\tilde\psi_s\rangle_{\tilde A_s\tilde B_s}|0\rangle_{\tilde A_F}|0\rangle_{\tilde B_F}$ as in (2), where
--   $$|\tilde\psi_k\rangle_{\tilde A_k\tilde B_k}=\cos\theta_k|00\rangle_{\tilde A_k\tilde B_k}-\sin\theta_k|11\rangle_{\tilde A_k\tilde B_k} \tag{3}$$
--   are two-mode fermion squeezed states entangling $\tilde A_k$ and $\tilde B_k$, and all remaining modes of $\tilde A$ and $\tilde B$ are in their vacuum.
--
--   This is the fermionic analogue of the Schmidt decomposition of pure bosonic Gaussian states: whatever the partition, the entanglement of a pure fermion Gaussian state consists of independent entangled mode pairs, with the same structure as the BCS wave function.
--
--   **Formalization Note.** The factors $\cos\theta_k-\sin\theta_k\tilde A_k^\dagger\tilde B_k^\dagger$ are even operators on disjoint pairs and commute, so the order of the product is immaterial. Locality means that each $\tilde A_i$ is a linear combination of the $A_j$ and $A_j^\dagger$ only, and each $\tilde B_j$ of the $B$-modes only.
--
--   Differences from the source:
--   - reading: the tensor product (2) of states on mode pairs → an operator product applied to a joint vacuum of all new modes; reason: a fermionic Fock space has no natural tensor factorization (p.8), and p.6 describes the pairs as T_i|00⟩ relative to the common vacuum; |11⟩ = Ã†B̃†|00⟩
--   - generalization: Fock space of the N modes → any finite-dimensional representation of the anticommutation relations; reason: the Fock space is an instance
--   - generalization: pure state of the form (4), ρ = ⊗ρ̃_k with |λ_k| = 1 → each factor ρ̃_k fixes ψ (IsPureGaussian); reason: implied by ρ = |ψ⟩⟨ψ| = ∏ρ̃_k, and equivalent to it in the Fock representation
--   - generalization: "entangling the modes Ã_k and B̃_k" → θ_k ∈ (0, π/4]; reason: a stronger conclusion, the normalization of the proof (λ ≥ 0, κ > 0); it makes both coefficients of (3) nonzero
--   - encoding: a partition of the N modes into A and B, and re-ordered new modes → mode index α ⊕ β, and pairs given by injective maps p_A, p_B; reason: relabelling only, since the anticommutation relations do not depend on an order of the modes
-- source:
--   Botero–Reznik, arXiv:quant-ph/0404176v3, main result, eqs. (2)–(3), p.2

import Mathlib
import Definitions.Def_FermionModewise_IsCanonicalFamily
import Definitions.Def_FermionModewise_IsPureGaussian
import Definitions.Def_FermionModewise_squeezeFactor

open Matrix

namespace FermionModewise

/-- **Main result: BCS-like modewise decomposition** (Botero–Reznik, arXiv:quant-ph/0404176v3, main
result, eqs. (2)–(3), p.2). Let `N` fermion modes `b` satisfying the anticommutation relations be
partitioned into `A = {A_1, …, A_m}` (indexed by `α`) and `B = {B_1, …, B_n}` (indexed by `β`), and
let `ψ` be a pure fermion Gaussian state. Then there are `s ≤ min(m, n)`, new modes
`Ã = {Ã_1, …, Ã_m}` and `B̃ = {B̃_1, …, B̃_n}` obtained from `A` and from `B` by local canonical
transformations, an injective pairing `k ↦ (Ã_{pA k}, B̃_{pB k})` for `k < s`, angles
`θ_k ∈ (0, π/4]`, and a unit vector `vac` annihilated by every `Ã_i` and every `B̃_j`, such that
```
ψ = ∏_{k<s} (cos θ_k − sin θ_k Ã_{pA k}† B̃_{pB k}†) vac,
```
i.e. `ψ` is the product of the two-mode squeezed states `cos θ_k|00⟩ − sin θ_k|11⟩` (3) on the
pairs and the vacuum of all remaining modes.

**Formalization Note.** In Lean the new families are `aNew` (for `Ã`) and `bNew` (for `B̃`). A fermionic Fock space has no literal tensor factorization (p.8), so the
product (2) is read as an operator product on the joint vacuum `vac` of all new modes, as on p.6
(`T_i|00⟩`); `|11⟩ = Ã†B̃†|00⟩`. The factors are even operators on disjoint pairs and commute, so
the `List.ofFn` order is a choice of presentation only. The partition is `α ⊕ β`; locality is
`IsCanonicalFamily (b ∘ Sum.inl) Ã` and `IsCanonicalFamily (b ∘ Sum.inr) B̃`. "Entangling" is
`0 < θ_k ≤ π/4`, so both coefficients of (3) are nonzero. Any finite-dimensional representation
of the anticommutation relations is allowed, and mode sets may be empty. -/
theorem main_result {ι α β : Type} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (b : α ⊕ β → Matrix ι ι ℂ) (hb : IsCAR b) (ψ : ι → ℂ)
    (hψ : IsPureGaussian b ψ) :
    ∃ (s : ℕ) (aNew : α → Matrix ι ι ℂ) (bNew : β → Matrix ι ι ℂ) (pA : Fin s ↪ α) (pB : Fin s ↪ β)
      (θ : Fin s → ℝ) (vac : ι → ℂ),
      s ≤ min (Fintype.card α) (Fintype.card β) ∧
      IsCanonicalFamily (b ∘ Sum.inl) aNew ∧ IsCanonicalFamily (b ∘ Sum.inr) bNew ∧
      (∀ k, 0 < θ k ∧ θ k ≤ Real.pi / 4) ∧
      star vac ⬝ᵥ vac = 1 ∧ (∀ i, aNew i *ᵥ vac = 0) ∧ (∀ j, bNew j *ᵥ vac = 0) ∧
      ψ = (List.ofFn fun k => squeezeFactor (aNew (pA k)) (bNew (pB k)) (θ k)).prod *ᵥ vac := by sorry

end FermionModewise
