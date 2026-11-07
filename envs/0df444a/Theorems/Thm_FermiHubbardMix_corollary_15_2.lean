-- Prove2me | Theorems.Thm_FermiHubbardMix_corollary_15_2
-- name    : FermiHubbardMix.corollary_15_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:36:01.076475+00:00
-- url     : https://prove2.me/theorems/60b53d26-8318-4e96-8d55-9b6d0df13682
-- title:
--   Corollary 15.2 — Fermi–Hubbard: $\|e^{t\mathcal L_{\mathrm{FR}}}(\rho)-\sigma\|_1\le\varepsilon$ for $\beta t_{\max}\le d^{-3}/(2^{16}\cdot300)$, $t\ge2\log(4n/\varepsilon)$
-- statement:
--   Let $\Lambda$ be $n$ sites of a $d$-dimensional lattice with edge set $E_\Lambda$, and let $H_{\mathrm{FH}}$ be the spin-$\tfrac12$ Fermi–Hubbard Hamiltonian on $(\Lambda,E_\Lambda)$ with hopping amplitudes $t_{ij}\in\mathbb R$ and arbitrary onsite couplings $U_i,\mu_i\in\mathbb R$. Assume
--   $$
--   t_{\max}=\max_{\{i,j\}\in E_\Lambda}|t_{ij}|>0 .
--   $$
--   For every inverse temperature $\beta>0$ with
--   $$
--   \beta\,t_{\max}\le\frac{d^{-3}}{2^{16}\cdot300},
--   $$
--   let $\sigma=e^{-\beta H_{\mathrm{FH}}}/\operatorname{tr}(e^{-\beta H_{\mathrm{FH}}})$ be the Gibbs state and $\mathcal L_{\mathrm{FR}}$ the field-resonant Lindbladian. Then for every fermionic density operator $\rho$, every $\varepsilon\in(0,1]$ and every time $t\ge2\log(4n/\varepsilon)$,
--   $$
--   \bigl\|e^{t\mathcal L_{\mathrm{FR}}}(\rho)-\sigma\bigr\|_1\le\varepsilon .
--   $$
--   The temperature need only be high compared with the hopping amplitude; the repulsions $U_i$ and chemical potentials $\mu_i$ are unrestricted, and the mixing time is logarithmic in $n$.
--
--   Differences from the source:
--   - generalization: Λ is n sites of a d-dimensional lattice with its edge set → any finite simple graph with every degree ≤ 2d; reason: the proof uses the lattice only through 'each site has at most 2d neighbors'; every finite piece of ℤ^d with nearest-neighbour edges is such a graph
--   - generalization: L_FR of H_FH (Definition 13.4; v_i is diagonal in the occupation basis) → L_FR built from any onsite eigenbasis F : FRData of H_FH, for every such F; reason: U_i = I with λ the diagonal entries is the paper's choice; any other admissible choice is the conjugation of Remark 13.3
--   - encoding: a fixed ordering of the modes of Λ × [m]; Fock space with operators c_{i,a} → any bijection ord : Λ × Fin m ≃ Fin N; c_k = (γ_{2k} + iγ_{2k+1})/2 from the published Jordan–Wigner Majoranas; reason: the same Fock space and the same CAR operators (proved in the verification files); the paper's results hold for every fixed ordering
--   - encoding: P^i_{µν} = ι_{{i}}(|µ⟩⟨ν|) → c†_µ Π^{{i}}_0 (c†_ν)†; reason: equal up to signs s_µ s_ν ∈ {±1}; the diagonal units coincide and every Lindbladian is quadratic in each jump
--   - encoding: operator-valued integrals (17), (18) and L_diss,B → entrywise Bochner integrals, superoperators as the linear extension of their values on matrix units; reason: the integrands are Gaussian-dominated, so the entrywise integrals are the paper's and the maps are linear
--   - encoding: βt_max ≤ d^{-3}/(2^{16}·300) → d³·(2^{16}·300)·(β t_max) ≤ 1; reason: division-free form; equal for d ≥ 1, and t_max > 0 forces an edge, so d ≥ 1
--   - encoding: hopping amplitudes t_ij on the edges {i,j} ∈ E, spins ↑, ↓, t_max = max over edges → t : Sym2 Λ → ℝ (one real per unordered pair, only edges used, zero allowed), ↑ = mode 0 and ↓ = mode 1 of Fin 2, t_max = ⨆ over G.edgeFinset; reason: w_{{i,j}} is indexed by the unordered pair, so t_ij = t_ji; the supremum over the finite edge set is its maximum when an edge exists, which t_max > 0 forces
-- source:
--   Bakshi, Moitra, Tan, Algorithmic Aspects of the Fermi–Hubbard Model, arXiv:2604.08408 (held version, sha256 055b8f8f…), Corollary 15.2, p.68

import Mathlib
import Definitions.Def_FermiHubbardMix_fermiHubbard
import Definitions.Def_FermiHubbardMix_FRData
import Definitions.Def_FermiHubbardMix_semigroup
import Definitions.Def_FermiHubbardMix_gibbs
import Definitions.Def_WildeQIT_traceNorm
open scoped BigOperators
open Matrix
noncomputable section

namespace FermiHubbardMix

/-- **Corollary 15.2 (Rapid mixing for the Fermi–Hubbard model on a `d`-dimensional lattice)** (Bakshi, Moitra, Tan, *Algorithmic Aspects of the Fermi–Hubbard Model*, arXiv:2604.08408 (held version, sha256 055b8f8f…),
p.68). Let `H_FH` be the spin-1/2 Fermi–Hubbard Hamiltonian (Example 11.8) on `n` sites with real
hopping amplitudes `t_{ij}` on the edges and arbitrary onsite couplings `U_i, µ_i ∈ ℝ`, and assume
`t_max = max_{{i,j} ∈ E} |t_{ij}| > 0`. For every `β > 0` with `βt_max ≤ d^{-3}/(2^{16}·300)`, let
`σ = e^{-βH_FH}/tr(e^{-βH_FH})` and `L_FR` the field-resonant Lindbladian. Then for every fermionic
density operator `ρ`, every `ε ∈ (0, 1]` and every `t ≥ 2 log(4n/ε)`, `‖e^{tL_FR}(ρ) - σ‖₁ ≤ ε`.

**Formalization Note** The `d`-dimensional lattice is any finite simple graph in which every site
has at most `2d` neighbours (the only property of the lattice the proof uses). The threshold is
`d³·2^{16}·300·βt_max ≤ 1`. The statement holds for every mode ordering `ord` and every onsite
eigenbasis `F` (for Fermi–Hubbard the occupation basis, `U_i = I`, is one). Spin `↑` is mode `0`,
`↓` mode `1`; `n = |Λ|`. -/
theorem corollary_15_2 {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}
    (ord : Λ × Fin 2 ≃ Fin N) (d : ℕ) (G : SimpleGraph Λ) [DecidableRel G.Adj]
    (hdeg : ∀ i, G.degree i ≤ 2 * d) (t : Sym2 Λ → ℝ) (U μ : Λ → ℝ) (htmax : 0 < tmax G t)
    (β : ℝ) (hβ : 0 < β) (hβt : (d : ℝ) ^ 3 * (2 ^ 16 * 300) * (β * tmax G t) ≤ 1)
    (F : FRData ord (fhHam ord G t U μ)) (ρ : Op N) (hρ : IsDensity ρ) (ε : ℝ) (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) (s : ℝ) (hs : 2 * Real.log (4 * Fintype.card Λ / ε) ≤ s) :
    WildeQIT.traceNorm (semigroup (lindFR ord (fhHam ord G t U μ) F β) s ρ -
      gibbs β (fhHam ord G t U μ).ham) ≤ ε := by sorry

end FermiHubbardMix
