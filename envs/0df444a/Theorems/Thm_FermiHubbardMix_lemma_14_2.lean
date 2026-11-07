-- Prove2me | Theorems.Thm_FermiHubbardMix_lemma_14_2
-- name    : FermiHubbardMix.lemma_14_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:36:43.99371+00:00
-- url     : https://prove2.me/theorems/28498dd6-dea0-49b1-9267-05dd947f1a1d
-- title:
--   Lemma 14.2 — update matrix $(1+72\cdot16^m\delta^2)I+\delta Q^{(i)}_{\mathrm{cohe}}$ of the coherent step
-- statement:
--   Assume $0<\beta\le1/(12\zeta)$. For every $\delta\ge0$, the coherent Euler step $\Phi^{(\delta)}_{i,\mathrm{cohe}}(X)=X-i\delta\sum_{B\in\mathcal B_i}[C_B,X]$ of the field-resonant Lindbladian has the fermionic update matrix
--   $$
--   (1+72\cdot16^m\delta^2)I+\delta Q^{(i)}_{\mathrm{cohe}},\qquad Q^{(i)}_{\mathrm{cohe}}=24\cdot4^m\sum_{r\ge1}(6\beta\zeta)^rE_{\mathfrak B(\{i\},r)}.
--   $$
--   Here $E_S=e_Se_S^{\mathsf T}$.
--
--   Differences from the source:
--   - encoding: a fixed ordering of the modes of Λ × [m]; Fock space with operators c_{i,a} → any bijection ord : Λ × Fin m ≃ Fin N; c_k = (γ_{2k} + iγ_{2k+1})/2 from the published Jordan–Wigner Majoranas; reason: the same Fock space and the same CAR operators (proved in the verification files); the paper's results hold for every fixed ordering
--   - encoding: P^i_{µν} = ι_{{i}}(|µ⟩⟨ν|) → c†_µ Π^{{i}}_0 (c†_ν)†; reason: equal up to signs s_µ s_ν ∈ {±1}; the diagonal units coincide and every Lindbladian is quadratic in each jump
--   - encoding: operator-valued integrals (17), (18) and L_diss,B → entrywise Bochner integrals, superoperators as the linear extension of their values on matrix units; reason: the integrands are Gaussian-dominated, so the entrywise integrals are the paper's and the maps are linear
--   - generalization: Section 14 assumes every v_i diagonal in the occupation basis with min ε_µ = 0 (Definition 13.4) → any onsite terms with any onsite eigenbasis F : FRData (even unitaries U_i ∈ 𝔄_{{i}} with U_i v_i U_i† diagonal); jumps U_i† P^i_{µν} U_i; evolution under H; reason: U_i = I and λ = ε recovers the page; for general U this is the paper's conjugation of Remark 13.3, under which every quantity in the statement is invariant
--   - encoding: 0 < β ≤ 1/(12ζ) → 0 < β and 12ζβ ≤ 1; reason: division-free form; the paper reads 1/0 as +∞, Lean's 1/0 = 0 would make the hypothesis false at ζ = 0
--   - encoding: Φ : 𝔄^ev_Λ → 𝔄^ev_Λ has a fermionic update matrix Q → Φ is a linear map on all operators; IsUpdateMatrix asserts that Φ preserves evenness, Hermiticity and trace on even operators and the cost condition; reason: the restriction to even operators is all that is constrained; Definition 12.10 presupposes the preservation properties
--   - encoding: ∑_{r≥1} c^r E_{𝔅({i},r)} → tsum over r of c^{r+1} • blockOnes (ball (r+1)); reason: the same convergent series (c ≤ 1/2 under the hypothesis), reindexed from r ≥ 1
-- source:
--   Bakshi, Moitra, Tan, Algorithmic Aspects of the Fermi–Hubbard Model, arXiv:2604.08408 (held version, sha256 055b8f8f…), Lemma 14.2, p.63

import Mathlib
import Definitions.Def_FermiHubbardMix_eulerStep
import Definitions.Def_FermiHubbardMix_w1
import Definitions.Def_FermiHubbardMix_hgDist
open scoped BigOperators
open Matrix
noncomputable section

namespace FermiHubbardMix

/-- **Lemma 14.2 (Update matrix of the coherent evolution)** (Bakshi, Moitra, Tan, *Algorithmic Aspects of the Fermi–Hubbard Model*, arXiv:2604.08408 (held version, sha256 055b8f8f…), p.63). Assume `0 < β ≤ 1/(12ζ)`.
For every `δ ≥ 0`, `Φ^{(δ)}_{i,cohe}(X) = X - iδ ∑_{B ∈ B_i} [C_B, X]` has the fermionic update matrix
`(1 + 72·16^m δ²) I + δ Q^{(i)}_cohe`, `Q^{(i)}_cohe = 24·4^m ∑_{r ≥ 1} (6βζ)^r E_{𝔅({i},r)}`.

**Formalization Note** `E_S = e_S e_Sᵀ` is `blockOnes S`; the series over `r ≥ 1` is a `tsum` indexed
by `r + 1`. `β ≤ 1/(12ζ)` is `12ζβ ≤ 1`. -/
theorem lemma_14_2 {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {m N : ℕ}
    (ord : Λ × Fin m ≃ Fin N) (H : HamData Λ N) (hH : H.IsLocal ord) (F : FRData ord H) (β : ℝ)
    (hβ : 0 < β) (hβζ : 12 * H.zeta * β ≤ 1) (i : Λ) (δ : ℝ) (hδ : 0 ≤ δ) :
    IsUpdateMatrix ord (cohStep ord H F β i δ)
      ((1 + 72 * 16 ^ m * δ ^ 2) • (1 : Matrix Λ Λ ℝ) +
        δ • ((24 * 4 ^ m : ℝ) • ∑' r : ℕ, (6 * β * H.zeta) ^ (r + 1) •
          blockOnes (hgBall H.edges {i} (r + 1)))) := by sorry

end FermiHubbardMix
