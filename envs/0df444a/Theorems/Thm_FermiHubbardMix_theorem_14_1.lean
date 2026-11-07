-- Prove2me | Theorems.Thm_FermiHubbardMix_theorem_14_1
-- name    : FermiHubbardMix.theorem_14_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:36:07.303809+00:00
-- url     : https://prove2.me/theorems/a3bebf26-ad83-40fc-86d2-d6a909528b5f
-- title:
--   Theorem 14.1 — update matrix $(1+160\cdot16^m\delta^2)I+\delta Q^{(i)}$ of $\mathcal I+\delta\mathcal L_{\mathrm{FR},i}$
-- statement:
--   Assume $0<\beta\le1/(12\zeta)$. For every $0\le\delta\le1/(\kappa_\star2^{m+1})$, the map $\Phi^{(\delta)}_i=\mathcal I+\delta\mathcal L_{\mathrm{FR},i}$ has the fermionic update matrix
--   $$
--   (1+160\cdot16^m\delta^2)I+\delta Q^{(i)},\qquad Q^{(i)}=-\kappa_\star E_{\{i\}}+40\cdot4^m\sum_{r\ge1}(6\beta\zeta)^rE_{\mathfrak B(\{i\},r)}.
--   $$
--   The negative diagonal term $-\kappa_\star E_{\{i\}}$ is the local contraction; the tail is controlled by the coupling strength alone.
--
--   Differences from the source:
--   - encoding: a fixed ordering of the modes of Λ × [m]; Fock space with operators c_{i,a} → any bijection ord : Λ × Fin m ≃ Fin N; c_k = (γ_{2k} + iγ_{2k+1})/2 from the published Jordan–Wigner Majoranas; reason: the same Fock space and the same CAR operators (proved in the verification files); the paper's results hold for every fixed ordering
--   - encoding: P^i_{µν} = ι_{{i}}(|µ⟩⟨ν|) → c†_µ Π^{{i}}_0 (c†_ν)†; reason: equal up to signs s_µ s_ν ∈ {±1}; the diagonal units coincide and every Lindbladian is quadratic in each jump
--   - encoding: operator-valued integrals (17), (18) and L_diss,B → entrywise Bochner integrals, superoperators as the linear extension of their values on matrix units; reason: the integrands are Gaussian-dominated, so the entrywise integrals are the paper's and the maps are linear
--   - generalization: Section 14 assumes every v_i diagonal in the occupation basis with min ε_µ = 0 (Definition 13.4) → any onsite terms with any onsite eigenbasis F : FRData (even unitaries U_i ∈ 𝔄_{{i}} with U_i v_i U_i† diagonal); jumps U_i† P^i_{µν} U_i; evolution under H; reason: U_i = I and λ = ε recovers the page; for general U this is the paper's conjugation of Remark 13.3, under which every quantity in the statement is invariant
--   - encoding: 0 < β ≤ 1/(12ζ) → 0 < β and 12ζβ ≤ 1; reason: division-free form; the paper reads 1/0 as +∞, Lean's 1/0 = 0 would make the hypothesis false at ζ = 0
--   - encoding: 0 ≤ δ ≤ 1/(κ⋆2^{m+1}) → 0 ≤ δ and κ⋆ 2^{m+1} δ ≤ 1; reason: division-free form of the same condition
--   - encoding: Φ : 𝔄^ev_Λ → 𝔄^ev_Λ has a fermionic update matrix Q → Φ is a linear map on all operators; IsUpdateMatrix asserts that Φ preserves evenness, Hermiticity and trace on even operators and the cost condition; reason: the restriction to even operators is all that is constrained; Definition 12.10 presupposes the preservation properties
--   - encoding: ∑_{r≥1} c^r E_{𝔅({i},r)} → tsum over r of c^{r+1} • blockOnes (ball (r+1)); reason: the same convergent series (c ≤ 1/2 under the hypothesis), reindexed from r ≥ 1
-- source:
--   Bakshi, Moitra, Tan, Algorithmic Aspects of the Fermi–Hubbard Model, arXiv:2604.08408 (held version, sha256 055b8f8f…), Theorem 14.1, p.62

import Mathlib
import Definitions.Def_FermiHubbardMix_FRData
import Definitions.Def_FermiHubbardMix_w1
import Definitions.Def_FermiHubbardMix_hgDist
open scoped BigOperators
open Matrix
noncomputable section

namespace FermiHubbardMix

/-- **Theorem 14.1 (Update matrix of the fermionic Lindbladian evolution at a site)** (Bakshi, Moitra, Tan, *Algorithmic Aspects of the Fermi–Hubbard Model*, arXiv:2604.08408 (held version, sha256 055b8f8f…), p.62).
Assume `0 < β ≤ 1/(12ζ)`. For every `0 ≤ δ ≤ 1/(κ⋆2^{m+1})`, `Φ^{(δ)}_i = ℐ + δ L_FR,i` has the
fermionic update matrix `(1 + 160·16^m δ²) I + δ Q^{(i)}`,
`Q^{(i)} = -κ⋆ E_{{i}} + 40·4^m ∑_{r ≥ 1} (6βζ)^r E_{𝔅({i},r)}`.

**Formalization Note** `E_S = e_S e_Sᵀ` is `blockOnes S`; the series is a `tsum` indexed by `r + 1`;
`β ≤ 1/(12ζ)` is `12ζβ ≤ 1` and `δ ≤ 1/(κ⋆2^{m+1})` is `κ⋆ 2^{m+1} δ ≤ 1`. -/
theorem theorem_14_1 {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {m N : ℕ}
    (ord : Λ × Fin m ≃ Fin N) (H : HamData Λ N) (hH : H.IsLocal ord) (F : FRData ord H) (β : ℝ)
    (hβ : 0 < β) (hβζ : 12 * H.zeta * β ≤ 1) (i : Λ) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ1 : kappaStar * 2 ^ (m + 1) * δ ≤ 1) :
    IsUpdateMatrix ord (LinearMap.id + (δ : ℂ) • lindFRSite ord H F β i)
      ((1 + 160 * 16 ^ m * δ ^ 2) • (1 : Matrix Λ Λ ℝ) +
        δ • (-(kappaStar • blockOnes ({i} : Set Λ)) + (40 * 4 ^ m : ℝ) • ∑' r : ℕ,
          (6 * β * H.zeta) ^ (r + 1) • blockOnes (hgBall H.edges {i} (r + 1)))) := by sorry

end FermiHubbardMix
