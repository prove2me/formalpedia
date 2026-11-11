-- Prove2me | Theorems.Thm_DistQuantumQuery_lemma_7_6
-- name    : DistQuantumQuery.lemma_7_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:18:18.448321+00:00
-- url     : https://prove2.me/theorems/ce301958-9b08-40b1-ac6d-e3e4a52de6b6
-- title:
--   Lemma 7.6 — $E^\downarrow_\Gamma$ maps $|\eta\rangle\langle\eta|$ to $|\mu\rangle\langle\mu|$ and valid targets of $f\circ g$ to valid targets of $f$
-- statement:
--   Let $g:\Sigma_g\to\{0,1\}$ be a decision problem, $\nu_0,\nu_1$ distributions supported on $g^{-1}(0)$ and $g^{-1}(1)$ (i.e. $\nu_b(x)\ne0\Rightarrow g(x)=b$), and $\Gamma\in L(\Sigma_g)$ real symmetric with $\Gamma\circ\Delta_g=\Gamma$ and $\langle\nu_0|\Gamma|\nu_1\rangle=\|\Gamma\|=1$. Then:
--
--   1. For a distribution $\mu$ on $\Sigma\subseteq\{0,1\}^n$ and $\eta=\mu\circ(\nu_0,\nu_1)$: $E^\downarrow_\Gamma(|\eta\rangle\langle\eta|)=|\mu\rangle\langle\mu|$.
--   2. For a search problem $f\subseteq\Sigma\times\Omega$ and $\varepsilon\in[0,1)$: for every $\Psi\in\mathcal G^\eta_\varepsilon(f\circ g)$, $E^\downarrow_\Gamma(\Psi\circ|\eta\rangle\langle\eta|)=\Psi^\downarrow\circ|\mu\rangle\langle\mu|$ for some $\Psi^\downarrow\in\mathcal G^\mu_\varepsilon(f)$.
--   3. For a functional problem $f:\Sigma\to\Omega$ and $\delta\in[0,1]$: for every $\Psi\in\mathcal R^\eta_\delta(f\circ g)$, $E^\downarrow_\Gamma(\Psi\circ|\eta\rangle\langle\eta|)=\Psi^\downarrow\circ|\mu\rangle\langle\mu|$ for some $\Psi^\downarrow\in\mathcal R^\mu_\delta(f)$.
--
--   Matrices indexed by $\Sigma$ and $\mathbf g^{-1}(\Sigma)$ are extended by zero to $\{0,1\}^n$ and $\Sigma_g^n$.
--
--   **Formalization Note** The composed search problem is $(f\circ g)(x)=f(\mathbf g(x))$. The extensions by zero are explicit, and each identity is an equality of matrices on all of $\{0,1\}^n$.
--
--   Differences from the source:
--   - encoding: Σ ⊂ {0,1}^n with positions [n] → Σ a Finset of bit strings ι → Bool over a finite type ι of positions; reason: relabelling positions; ι = Fin n is the source's case and every finite ι is a relabelling of some Fin n
--   - encoding: G^μ_ε(f): max_{W ∈ W^μ_f} F(W ∘ |μ⟩⟨μ|, Ψ ∘ |μ⟩⟨μ|) ≥ √(1−ε) → ∃ W ∈ W^μ_f with F ≥ √(1−ε); reason: the source writes max, i.e. the maximum is attained
--   - reading: identities whose result is “restricted back to Σ” → the identities hold as equalities of the zero-extended matrices on all of {0,1}^n; reason: E↓_Γ of a matrix supported on g⁻¹(Σ) × g⁻¹(Σ) is supported on Σ × Σ, so the full equality is the stronger reading
-- source:
--   Ben-David, Ebtehaj, Distributional Quantum Query Complexity, arXiv:2610.06835 (held version, sha256 6334ffaf…), Lemma 7.6, pp.58–59

import Mathlib
import Definitions.Def_DistQuantumQuery_Adv
import Definitions.Def_DistQuantumQuery_rAdv
import Definitions.Def_DistQuantumQuery_liftUp

open scoped Matrix ENNReal ComplexOrder Topology

namespace DistQuantumQuery

/-- **Lemma 7.6** (Ben-David, Ebtehaj, *Distributional Quantum Query Complexity*, arXiv:2610.06835,
held version, sha256 6334ffaf…, Lemma 7.6, pp.58–59). Let `g`, `ν₀, ν₁` be as in Theorem 7.1 and
`Γ ∈ L(Σ_g)` real symmetric with `Γ ∘ Δ_g = Γ` and `⟨ν₀|Γ|ν₁⟩ = ‖Γ‖ = 1`. Then:
(i) for a distribution `μ` on `Σ ⊆ {0,1}^n` and `η = μ ∘ (ν₀, ν₁)`, `E↓_Γ(|η⟩⟨η|) = |μ⟩⟨μ|`;
(ii) for a search problem `f ⊆ Σ × Ω` and `ε ∈ [0,1)`, every `Ψ ∈ G^η_ε(f ∘ g)` has
`E↓_Γ(Ψ ∘ |η⟩⟨η|) = Ψ↓ ∘ |μ⟩⟨μ|` for some `Ψ↓ ∈ G^μ_ε(f)`;
(iii) for a functional problem `f : Σ → Ω` and `δ ∈ [0,1]`, every `Ψ ∈ R^η_δ(f ∘ g)` has
`E↓_Γ(Ψ ∘ |η⟩⟨η|) = Ψ↓ ∘ |μ⟩⟨μ|` for some `Ψ↓ ∈ R^μ_δ(f)`.
Matrices indexed by `Σ` and `g⁻¹(Σ)` are extended by zero to `{0,1}^n` and `Σ_g^n`.

**Formalization Note** The extensions by zero are explicit (`extOuter`, `extComp`); the
identities are stated as equalities of the extended matrices on all of `{0,1}^n`, which also
gives the restricted identities. The composed relation of a search problem `R` is
`(x, s) ↦ R(g(x), s)`; `η` is `compDist`. "As in Theorem 7.1": `ν₀, ν₁` distributions supported on
`g⁻¹(0)`, `g⁻¹(1)`. The search problem is a total relation. -/
theorem lemma_7_6 {ι κ Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype Ω] [DecidableEq Ω]
    (Sg : Finset (κ → Bool)) (g : Sg → Bool) (ν₀ ν₁ : Sg → ℝ) (hν₀ : IsDist ν₀) (hν₁ : IsDist ν₁)
    (hs₀ : ∀ x, ν₀ x ≠ 0 → g x = false) (hs₁ : ∀ x, ν₁ x ≠ 0 → g x = true)
    (Γ : Matrix Sg Sg ℂ) (hΓreal : ∀ x y, (Γ x y).im = 0) (hΓsymm : Γᵀ = Γ) (hΓg : Γ ⊙ disagree g = Γ)
    (hΓν : star (muKet ν₀) ⬝ᵥ (Γ *ᵥ muKet ν₁) = 1) (hΓnorm : opNorm Γ = 1)
    (S : Finset (ι → Bool)) (μ : S → ℝ) (hμ : IsDist μ)
    (R : S → Ω → Prop) (hR : ∀ x, ∃ s, R x s) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (f : S → Ω) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    -- (i)
    liftDown g Γ (extComp (muMat (compDist g μ ν₀ ν₁))) = extOuter S (muMat μ) ∧
    -- (ii)
    (∀ Ψ ∈ Targets (compDist g μ ν₀ ν₁) (fun x s => R (compOuter x) s) ε,
      ∃ Ψd ∈ Targets μ R ε,
        liftDown g Γ (extComp (Ψ ⊙ muMat (compDist g μ ν₀ ν₁))) = extOuter S (Ψd ⊙ muMat μ)) ∧
    -- (iii)
    (∀ Ψ ∈ relaxedTargets (compDist g μ ν₀ ν₁) (compose f g) δ,
      ∃ Ψd ∈ relaxedTargets μ f δ,
        liftDown g Γ (extComp (Ψ ⊙ muMat (compDist g μ ν₀ ν₁))) =
          extOuter S (Ψd ⊙ muMat μ)) := by sorry

end DistQuantumQuery
