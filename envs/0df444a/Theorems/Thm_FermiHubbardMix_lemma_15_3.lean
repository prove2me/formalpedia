-- Prove2me | Theorems.Thm_FermiHubbardMix_lemma_15_3
-- name    : FermiHubbardMix.lemma_15_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:36:00.106181+00:00
-- url     : https://prove2.me/theorems/e9522bea-bce1-4347-89bf-409c5ab30596
-- title:
--   Lemma 15.3 — $\|D^{(\Phi)}\|_{1\to1}\le1-\delta/(2n)+160\cdot16^m\delta^2$
-- statement:
--   Let $H$ be a local fermionic Hamiltonian with onsite terms on $n$ sites, $m$ modes per site, whose multi-site part has bounded $L$-site degree-$D$ couplings. For every $0<\beta\le4^{-m}(DL)^{-3}/9600$ and every $\delta\in[0,1/(\kappa_\star2^{m+1})]$, let
--   $$
--   \Phi=\mathcal I+\frac\delta n\mathcal L_{\mathrm{FR}}=\frac1n\sum_{i\in\Lambda}\bigl(\mathcal I+\delta\mathcal L_{\mathrm{FR},i}\bigr),
--   $$
--   and let $D^{(\Phi)}$ be its Dobrushin influence matrix (for the summands $\Phi^{(\delta)}_i=\mathcal I+\delta\mathcal L_{\mathrm{FR},i}$). Then
--   $$
--   \|D^{(\Phi)}\|_{1\to1}\le1-\frac{\delta}{2n}+160\cdot16^m\delta^2 .
--   $$
--   For small $\delta$ the right side is below $1$: the Euler step contracts the Wasserstein norm.
--
--   Differences from the source:
--   - encoding: a fixed ordering of the modes of Λ × [m]; Fock space with operators c_{i,a} → any bijection ord : Λ × Fin m ≃ Fin N; c_k = (γ_{2k} + iγ_{2k+1})/2 from the published Jordan–Wigner Majoranas; reason: the same Fock space and the same CAR operators (proved in the verification files); the paper's results hold for every fixed ordering
--   - encoding: P^i_{µν} = ι_{{i}}(|µ⟩⟨ν|) → c†_µ Π^{{i}}_0 (c†_ν)†; reason: equal up to signs s_µ s_ν ∈ {±1}; the diagonal units coincide and every Lindbladian is quadratic in each jump
--   - encoding: operator-valued integrals (17), (18) and L_diss,B → entrywise Bochner integrals, superoperators as the linear extension of their values on matrix units; reason: the integrands are Gaussian-dominated, so the entrywise integrals are the paper's and the maps are linear
--   - generalization: Section 15 (through Definition 13.4) assumes every v_i diagonal in the occupation basis with min ε_µ = 0 (Definition 13.4) → any onsite terms with any onsite eigenbasis F : FRData (even unitaries U_i ∈ 𝔄_{{i}} with U_i v_i U_i† diagonal); jumps U_i† P^i_{µν} U_i; evolution under H; reason: U_i = I and λ = ε recovers the page; for general U this is the paper's conjugation of Remark 13.3, under which every quantity in the statement is invariant
--   - encoding: 0 < β ≤ 4^{-m}(DL)^{-3}/9600 and δ ≤ 1/(κ⋆2^{m+1}) → 0 < β, 9600·4^m(DL)³β ≤ 1, 0 ≤ δ, κ⋆2^{m+1}δ ≤ 1; reason: division-free form of the same conditions
-- source:
--   Bakshi, Moitra, Tan, Algorithmic Aspects of the Fermi–Hubbard Model, arXiv:2604.08408 (held version, sha256 055b8f8f…), Lemma 15.3, pp.68–69

import Mathlib
import Definitions.Def_FermiHubbardMix_FRData
import Definitions.Def_FermiHubbardMix_w1
open scoped BigOperators
open Matrix
noncomputable section

namespace FermiHubbardMix

/-- **Lemma 15.3 (Bounding the fermionic Dobrushin influence matrix)** (Bakshi, Moitra, Tan, *Algorithmic Aspects of the Fermi–Hubbard Model*, arXiv:2604.08408 (held version, sha256 055b8f8f…), pp.68–69). Let `H` be a
local fermionic Hamiltonian with onsite terms whose multi-site part has bounded `L`-site degree-`D`
couplings. For `0 < β ≤ 4^{-m}(DL)^{-3}/9600` and `δ ∈ [0, 1/(κ⋆2^{m+1})]`, let
`Φ = ℐ + (δ/n) L_FR = (1/n) ∑_i Φ^{(δ)}_i` with `Φ^{(δ)}_i = ℐ + δ L_FR,i`. Then
`‖D^{(Φ)}‖_{1→1} ≤ 1 - δ/(2n) + 160·16^m δ²` (`n = |Λ|`).

**Formalization Note** The thresholds are `9600·4^m(DL)³β ≤ 1` and `κ⋆2^{m+1}δ ≤ 1`. The Dobrushin
matrix is that of the family `Φ_i = ℐ + δ L_FR,i` (Definition 12.19). -/
theorem lemma_15_3 {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {m N : ℕ}
    (ord : Λ × Fin m ≃ Fin N) (H : HamData Λ N) (hH : H.IsLocal ord) (L D : ℕ)
    (hLD : H.BoundedCouplings L D) (β : ℝ) (hβ : 0 < β)
    (hβLD : 9600 * 4 ^ m * ((D : ℝ) * L) ^ 3 * β ≤ 1) (F : FRData ord H) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ1 : kappaStar * 2 ^ (m + 1) * δ ≤ 1) :
    norm11 (dobrushin ord fun i => LinearMap.id + (δ : ℂ) • lindFRSite ord H F β i) ≤
      1 - δ / (2 * Fintype.card Λ) + 160 * 16 ^ m * δ ^ 2 := by sorry

end FermiHubbardMix
