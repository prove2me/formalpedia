-- Prove2me | Theorems.Thm_FermiHubbardMix_lemma_12_20
-- name    : FermiHubbardMix.lemma_12_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:34:47.259282+00:00
-- url     : https://prove2.me/theorems/cb8826a1-a6d4-442a-be5b-eaecda8aecdf
-- title:
--   Lemma 12.20 — $\|\Phi(X)\|_{W_1}\le\|D^{(\Phi)}\|_{1\to1}\|X\|_{W_1}$
-- statement:
--   Let $\Phi_1,\dots,\Phi_n$ be linear maps of $\mathfrak A^{\mathrm{ev}}_\Lambda$ into itself that preserve trace and Hermiticity, $\Phi=\frac1n(\Phi_1+\dots+\Phi_n)$, and let $D^{(\Phi)}$ be the Dobrushin influence matrix. Then for every traceless Hermitian $X\in\mathfrak A^{\mathrm{ev}}_\Lambda$,
--   $$
--   \|\Phi(X)\|_{W_1}\le\|D^{(\Phi)}\|_{1\to1}\,\|X\|_{W_1}.
--   $$
--   So $\|D^{(\Phi)}\|_{1\to1}<1$ gives strict contraction in the fermionic Wasserstein norm.
--
--   Differences from the source:
--   - encoding: a fixed ordering of the modes of Λ × [m]; Fock space with operators c_{i,a} → any bijection ord : Λ × Fin m ≃ Fin N; c_k = (γ_{2k} + iγ_{2k+1})/2 from the published Jordan–Wigner Majoranas; reason: the same Fock space and the same CAR operators (proved in the verification files); the paper's results hold for every fixed ordering
--   - encoding: P^i_{µν} = ι_{{i}}(|µ⟩⟨ν|) → c†_µ Π^{{i}}_0 (c†_ν)†; reason: equal up to signs s_µ s_ν ∈ {±1}; the diagonal units coincide and every Lindbladian is quadratic in each jump
--   - encoding: Φ_i : 𝔄^ev_Λ → 𝔄^ev_Λ trace- and Hermiticity-preserving → linear maps on all operators with PreservesEvenHermTrace; reason: only the restriction to even operators enters; every map on 𝔄^ev_Λ extends
-- source:
--   Bakshi, Moitra, Tan, Algorithmic Aspects of the Fermi–Hubbard Model, arXiv:2604.08408 (held version, sha256 055b8f8f…), Lemma 12.20, p.58

import Mathlib
import Definitions.Def_FermiHubbardMix_w1
open scoped BigOperators
open Matrix
noncomputable section

namespace FermiHubbardMix

/-- **Lemma 12.20 (Contraction from Dobrushin influence)** (Bakshi, Moitra, Tan, *Algorithmic Aspects of the Fermi–Hubbard Model*, arXiv:2604.08408 (held version, sha256 055b8f8f…), p.58). Let
`Φ, Φ_1, …, Φ_n : 𝔄^ev_Λ → 𝔄^ev_Λ` be trace-preserving, Hermiticity-preserving linear maps with
`Φ = (1/n)(Φ_1 + ⋯ + Φ_n)` (Definition 12.19), and `D^{(Φ)}` the Dobrushin influence matrix. Then for
every traceless Hermitian `X ∈ 𝔄^ev_Λ`, `‖Φ(X)‖_{W₁} ≤ ‖D^{(Φ)}‖_{1→1} ‖X‖_{W₁}`. -/
theorem lemma_12_20 {Λ : Type*} [Fintype Λ] {m N : ℕ} (ord : Λ × Fin m ≃ Fin N)
    (Φs : Λ → Op N →ₗ[ℂ] Op N) (hΦ : ∀ i, PreservesEvenHermTrace (Φs i))
    (X : Op N) (hXh : X.IsHermitian) (hXe : IsEven X) (hX0 : X.trace = 0) :
    w1 ord (((Fintype.card Λ : ℂ)⁻¹ • ∑ i, Φs i) X) ≤ norm11 (dobrushin ord Φs) * w1 ord X := by sorry

end FermiHubbardMix
