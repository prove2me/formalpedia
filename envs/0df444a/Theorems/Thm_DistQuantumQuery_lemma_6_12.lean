-- Prove2me | Theorems.Thm_DistQuantumQuery_lemma_6_12
-- name    : DistQuantumQuery.lemma_6_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:18:20.313374+00:00
-- url     : https://prove2.me/theorems/8884f100-78f7-486d-8a30-2ecaebc6ddb3
-- title:
--   Lemma 6.12 — dual form $\mathrm{sfAdv}^{(\nu_0,\nu_1)}(g)=\max 1/\max_i\|\Gamma\circ\Delta_i\|$ over $\langle\nu_0|\Gamma|\nu_1\rangle=\|\Gamma\|=1$
-- statement:
--   Let $g:\Sigma\to\{0,1\}$ be a decision problem on $\Sigma\subseteq\{0,1\}^m$ and $\nu_0,\nu_1$ distributions supported on $g^{-1}(0)$ and $g^{-1}(1)$ (i.e. $\nu_b(x)\ne0\Rightarrow g(x)=b$). Then
--   $$
--   \mathrm{sfAdv}^{(\nu_0,\nu_1)}(g)=\max_{\Gamma=\Gamma^\dagger}\frac1{\max_i\|\Gamma\circ\Delta_i\|}\quad\text{s.t. }\langle\nu_0|\Gamma|\nu_1\rangle=\|\Gamma\|=1;\ \Gamma\circ\Delta_g=\Gamma,
--   $$
--   where $|\nu_b\rangle=\sum_{x\in g^{-1}(b)}\sqrt{\nu_b(x)}\,|x\rangle$. In particular, the value is finite and the maximum is attained by a real symmetric matrix $\Gamma$.
--
--   The maximizer is the universal hardness certificate for $g$ used to build the lifting map of the composition proof.
--
--   Differences from the source:
--   - encoding: Σ ⊂ {0,1}^n with positions [n] → Σ a Finset of bit strings ι → Bool over a finite type ι of positions; reason: relabelling positions; ι = Fin n is the source's case and every finite ι is a relabelling of some Fin n
--   - encoding: min / max / inf of measures, +∞ if unbounded; Q an integer → values in ℝ≥0∞ (Q in ℕ∞, cast to ℝ≥0∞); min/inf as ⨅, max/sup as ⨆; reason: same values, with ⊤ for +∞; no real cast that would send ⊤ to 0
--   - encoding: “max”/“min” attained; “the value is finite” → IsGreatest / IsLeast of the real objective sets, and the measure equals ENNReal.ofReal of the optimum; reason: attainment and finiteness written out
-- source:
--   Ben-David, Ebtehaj, Distributional Quantum Query Complexity, arXiv:2610.06835 (held version, sha256 6334ffaf…), Lemma 6.12, pp.53–54

import Mathlib
import Definitions.Def_DistQuantumQuery_sfAdv

open scoped Matrix ENNReal ComplexOrder Topology

namespace DistQuantumQuery

/-- **Lemma 6.12** (Ben-David, Ebtehaj, *Distributional Quantum Query Complexity*, arXiv:2610.06835,
held version, sha256 6334ffaf…, Lemma 6.12, pp.53–54). Let `g : Σ → {0,1}` be a decision problem on
`Σ ⊆ {0,1}^m` and `ν₀, ν₁` distributions supported on `g⁻¹(0)`, `g⁻¹(1)`. Then
`sfAdv^{(ν₀,ν₁)}(g) = max_{Γ = Γ†} 1 / max_i ‖Γ ∘ Δ_i‖ s.t. ⟨ν₀|Γ|ν₁⟩ = ‖Γ‖ = 1; Γ ∘ Δ_g = Γ`,
where `|ν_b⟩ = Σ_{x∈g⁻¹(b)} √ν_b(x)|x⟩`. In particular, the value is finite and the maximum is
attained by a real symmetric matrix `Γ`.

**Formalization Note** `|ν_b⟩` is `muKet ν_b` (supported on `g⁻¹(b)` by the support
hypotheses). "max" is `IsGreatest` in `ℝ≥0∞`; `1 / M` is `(ofReal M)⁻¹`. "Supported on" is
`ν_b(x) ≠ 0 → g(x) = b` (§2.4.3: `supp ν_b ⊆ g⁻¹(b)`). -/
theorem lemma_6_12 {κ : Type*} [Fintype κ] [DecidableEq κ] (Sg : Finset (κ → Bool))
    (g : Sg → Bool) (ν₀ ν₁ : Sg → ℝ) (hν₀ : IsDist ν₀) (hν₁ : IsDist ν₁)
    (hs₀ : ∀ x, ν₀ x ≠ 0 → g x = false) (hs₁ : ∀ x, ν₁ x ≠ 0 → g x = true) :
    let feas : Matrix Sg Sg ℂ → Prop := fun Γ => Γ.IsHermitian ∧
      star (muKet ν₀) ⬝ᵥ (Γ *ᵥ muKet ν₁) = 1 ∧ opNorm Γ = 1 ∧ Γ ⊙ disagree g = Γ
    sfAdv Sg g ν₀ ν₁ ≠ ⊤ ∧
    IsGreatest {v | ∃ Γ, feas Γ ∧ v = (ENNReal.ofReal (maxFilterNorm Γ (qfilters Sg)))⁻¹}
      (sfAdv Sg g ν₀ ν₁) ∧
    ∃ Γ, feas Γ ∧ (∀ x y, (Γ x y).im = 0) ∧ Γᵀ = Γ ∧
      sfAdv Sg g ν₀ ν₁ = (ENNReal.ofReal (maxFilterNorm Γ (qfilters Sg)))⁻¹ := by sorry

end DistQuantumQuery
