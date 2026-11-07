-- Prove2me | Theorems.Thm_FermiHubbardMix_corollary_15_2_rescaling
-- name    : FermiHubbardMix.corollary_15_2_rescaling
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:36:25.062256+00:00
-- url     : https://prove2.me/theorems/7fc06871-48bc-434a-b38a-f39bc269cbf6
-- title:
--   Proof of Corollary 15.2 (ii) — rescaling $H\to H/s$, $\beta\to s\beta$ leaves $\sigma$ and $\mathcal L_{\mathrm{FR}}$ unchanged
-- statement:
--   Let $H$ be a Hamiltonian with onsite terms, $F$ an onsite eigenbasis of $H$, $\beta>0$ and $s>0$. Then
--
--   1. $\sigma(s\beta,H/s)=\sigma(\beta,H)$;
--   2. the unitaries of $F$ also form an onsite eigenbasis of $H/s$ (with eigenvalues $\lambda/s$);
--   3. for every onsite eigenbasis $F'$ of $H/s$ with the same unitaries as $F$,
--   $$
--   \mathcal L_{\mathrm{FR}}(H/s,\,s\beta)=\mathcal L_{\mathrm{FR}}(H,\,\beta).
--   $$
--   With $s=2t_{\max}$ this is the second step of the proof of Corollary 15.2: "Rescale $\tilde H=H_{\mathrm{FH}}/(2t_{\max})$ and $\tilde\beta=2t_{\max}\beta$, which leaves the Gibbs state and the field-resonant Lindbladian unchanged."
--
--   Differences from the source:
--   - encoding: a fixed ordering of the modes of Λ × [m]; Fock space with operators c_{i,a} → any bijection ord : Λ × Fin m ≃ Fin N; c_k = (γ_{2k} + iγ_{2k+1})/2 from the published Jordan–Wigner Majoranas; reason: the same Fock space and the same CAR operators (proved in the verification files); the paper's results hold for every fixed ordering
--   - encoding: P^i_{µν} = ι_{{i}}(|µ⟩⟨ν|) → c†_µ Π^{{i}}_0 (c†_ν)†; reason: equal up to signs s_µ s_ν ∈ {±1}; the diagonal units coincide and every Lindbladian is quadratic in each jump
--   - encoding: operator-valued integrals (17), (18) and L_diss,B → entrywise Bochner integrals, superoperators as the linear extension of their values on matrix units; reason: the integrands are Gaussian-dominated, so the entrywise integrals are the paper's and the maps are linear
--   - generalization: H̃ = H_FH/(2t_max), β̃ = 2t_maxβ → every s > 0 and every Hamiltonian H, every onsite eigenbasis; reason: s = 2t_max and H = H_FH is the case used; the invariance holds for every scale
-- source:
--   Bakshi, Moitra, Tan, Algorithmic Aspects of the Fermi–Hubbard Model, arXiv:2604.08408 (held version, sha256 055b8f8f…), proof of Corollary 15.2, p.68

import Mathlib
import Definitions.Def_FermiHubbardMix_FRData
import Definitions.Def_FermiHubbardMix_gibbs
open scoped BigOperators
open Matrix
noncomputable section

namespace FermiHubbardMix

/-- **Proof of Corollary 15.2, second step** (Bakshi, Moitra, Tan, *Algorithmic Aspects of the Fermi–Hubbard Model*, arXiv:2604.08408 (held version, sha256 055b8f8f…), p.68): "Rescale `H̃ = H_FH/(2t_max)` and
`β̃ = 2t_maxβ`, which leaves the Gibbs state and the field-resonant Lindbladian unchanged." Stated for
every scale `s > 0` and every Hamiltonian: `σ(sβ, H/s) = σ(β, H)`; an onsite eigenbasis `F` of `H`
gives one of `H/s` with the same unitaries; and for every such eigenbasis `F'` of `H/s`,
`L_FR(H/s, sβ) = L_FR(H, β)`.

**Formalization Note** The corollary uses `s = 2t_max`. -/
theorem corollary_15_2_rescaling {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {m N : ℕ}
    (ord : Λ × Fin m ≃ Fin N) (H : HamData Λ N) (F : FRData ord H) (β : ℝ) (hβ : 0 < β) (s : ℝ)
    (hs : 0 < s) :
    gibbs (s * β) (H.smul s⁻¹).ham = gibbs β H.ham ∧
      (∃ F' : FRData ord (H.smul s⁻¹), F'.U = F.U) ∧
      ∀ F' : FRData ord (H.smul s⁻¹), F'.U = F.U →
        lindFR ord (H.smul s⁻¹) F' (s * β) = lindFR ord H F β := by sorry

end FermiHubbardMix
