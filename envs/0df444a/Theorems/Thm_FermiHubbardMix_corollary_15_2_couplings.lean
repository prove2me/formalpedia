-- Prove2me | Theorems.Thm_FermiHubbardMix_corollary_15_2_couplings
-- name    : FermiHubbardMix.corollary_15_2_couplings
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:35:52.180574+00:00
-- url     : https://prove2.me/theorems/7975e3dc-97ce-4c0c-bf09-c35e3a372c05
-- title:
--   Proof of Corollary 15.2 (i) — $H_{\mathrm{FH}}/(2t_{\max})$ has bounded $2$-site degree-$2d$ couplings
-- statement:
--   Let $(\Lambda,E)$ be a finite simple graph in which every site has at most $2d$ neighbours, and let $H_{\mathrm{FH}}$ be the spin-$\tfrac12$ Fermi–Hubbard Hamiltonian on it with real $t_{ij}$, $U_i$, $\mu_i$ and $t_{\max}=\max_{\{i,j\}\in E}|t_{ij}|>0$. Then:
--
--   1. the rescaled Hamiltonian $H_{\mathrm{FH}}/(2t_{\max})$ is a local fermionic Hamiltonian with onsite terms (Definition 11.7);
--   2. its multi-site part has bounded $2$-site degree-$2d$ couplings (Definition 4.1);
--   3. every hopping term satisfies $\|w_{\{i,j\}}\|\le2|t_{ij}|$.
--
--   This is the first step of the proof of Corollary 15.2 ("each site carries $m=2$ modes, each hopping term has support size two and norm at most $2t_{\max}$, and each site has at most $2d$ neighbors"), which reduces the corollary to Theorem 15.1 with $L=2$, $D=2d$.
--
--   Differences from the source:
--   - encoding: a fixed ordering of the modes of Λ × [m]; Fock space with operators c_{i,a} → any bijection ord : Λ × Fin m ≃ Fin N; c_k = (γ_{2k} + iγ_{2k+1})/2 from the published Jordan–Wigner Majoranas; reason: the same Fock space and the same CAR operators (proved in the verification files); the paper's results hold for every fixed ordering
--   - generalization: Λ is n sites of a d-dimensional lattice with its edge set → any finite simple graph with every degree ≤ 2d; reason: the proof uses the lattice only through 'each site has at most 2d neighbors'; every finite piece of ℤ^d with nearest-neighbour edges is such a graph
--   - generalization: each hopping term has norm at most 2t_max → ‖w_{i,j}‖ ≤ 2|t_ij| for every edge; reason: a stronger conclusion; 2|t_ij| ≤ 2t_max
--   - encoding: hopping amplitudes t_ij on the edges {i,j} ∈ E, spins ↑, ↓, t_max = max over edges → t : Sym2 Λ → ℝ (one real per unordered pair, only edges used, zero allowed), ↑ = mode 0 and ↓ = mode 1 of Fin 2, t_max = ⨆ over G.edgeFinset; reason: w_{{i,j}} is indexed by the unordered pair, so t_ij = t_ji; the supremum over the finite edge set is its maximum when an edge exists, which t_max > 0 forces
-- source:
--   Bakshi, Moitra, Tan, Algorithmic Aspects of the Fermi–Hubbard Model, arXiv:2604.08408 (held version, sha256 055b8f8f…), proof of Corollary 15.2, p.68

import Mathlib
import Definitions.Def_FermiHubbardMix_fermiHubbard
open scoped BigOperators
open Matrix
noncomputable section

namespace FermiHubbardMix

/-- **Proof of Corollary 15.2, first step** (Bakshi, Moitra, Tan, *Algorithmic Aspects of the Fermi–Hubbard Model*, arXiv:2604.08408 (held version, sha256 055b8f8f…), p.68): "Each site carries `m = 2` modes, each hopping
term has support size two and norm at most `2t_max`, and each site has at most `2d` neighbors." For
the Fermi–Hubbard Hamiltonian on a graph of maximum degree at most `2d` with `t_max > 0`, the
rescaled Hamiltonian `H_FH/(2t_max)` is a local fermionic Hamiltonian with onsite terms
(Definition 11.7) whose multi-site part has bounded `2`-site degree-`2d` couplings
(Definition 4.1), and every hopping term satisfies `‖w_{{i,j}}‖ ≤ 2|t_{ij}|`.

**Formalization Note** The `d`-dimensional lattice enters only through "each site has at most `2d`
neighbors", the hypothesis `∀ i, deg i ≤ 2d`. -/
theorem corollary_15_2_couplings {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}
    (ord : Λ × Fin 2 ≃ Fin N) (d : ℕ) (G : SimpleGraph Λ) [DecidableRel G.Adj]
    (hdeg : ∀ i, G.degree i ≤ 2 * d) (t : Sym2 Λ → ℝ) (U μ : Λ → ℝ) (htmax : 0 < tmax G t) :
    ((fhHam ord G t U μ).smul (2 * tmax G t)⁻¹).IsLocal ord ∧
      ((fhHam ord G t U μ).smul (2 * tmax G t)⁻¹).BoundedCouplings 2 (2 * d) ∧
      ∀ i j, G.Adj i j → opNorm ((fhHam ord G t U μ).w {i, j}) ≤ 2 * |t s(i, j)| := by sorry

end FermiHubbardMix
