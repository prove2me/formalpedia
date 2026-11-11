-- Prove2me | Theorems.Thm_DistQuantumQuery_proposition_6_3
-- name    : DistQuantumQuery.proposition_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:17:51.085918+00:00
-- url     : https://prove2.me/theorems/68580a1a-2b8e-478f-9c9b-33d63abc32dd
-- title:
--   Proposition 6.3 — minimax and decision dual forms of $\mathrm{rAdv}^\mu_\delta(f)$
-- statement:
--   Let $\Sigma\subseteq\{0,1\}^n$, $f:\Sigma\to\Omega$ a functional problem, $\mu$ a distribution and $\delta\in[0,1]$. Then
--   $$
--   \mathrm{rAdv}^\mu_\delta(f)=\max_{\Gamma=\Gamma^\dagger,\ \Gamma\circ I=0,\ \max_i\|\Gamma\circ\Delta_i\|\le1}\ \min_{\Psi\in\mathcal R^\mu_\delta(f)}\langle\Gamma,(J-\Psi)\circ|\mu\rangle\langle\mu|\rangle .
--   $$
--   Moreover, if $f$ is a decision problem, then
--   $$
--   \mathrm{rAdv}^\mu_\delta(f)=\max_{\Gamma=\Gamma^\dagger,\ \Gamma\circ\Delta_f=\Gamma,\ \max_i\|\Gamma\circ\Delta_i\|\le1}\ \langle\Gamma,\Delta_f\circ|\mu\rangle\langle\mu|\rangle-\delta\|\Gamma\| .
--   $$
--   In particular, the value is finite and both maxima are attained.
--
--   The decision form is the source of the dual characterization of $\mathrm{sfAdv}$ (Lemma 6.12).
--
--   Differences from the source:
--   - encoding: Σ ⊂ {0,1}^n with positions [n] → Σ a Finset of bit strings ι → Bool over a finite type ι of positions; reason: relabelling positions; ι = Fin n is the source's case and every finite ι is a relabelling of some Fin n
--   - encoding: min / max / inf of measures, +∞ if unbounded; Q an integer → values in ℝ≥0∞ (Q in ℕ∞, cast to ℝ≥0∞); min/inf as ⨅, max/sup as ⨆; reason: same values, with ⊤ for +∞; no real cast that would send ⊤ to 0
--   - encoding: the real number ⟨Γ, M⟩ for Hermitian Γ and Hermitian M (or Tr of a PSD matrix) → the real part of ⟨Γ, M⟩ (resp. of the trace); reason: the inner product is real under the stated hypotheses
--   - encoding: “max”/“min” attained; “the value is finite” → IsGreatest / IsLeast of the real objective sets, and the measure equals ENNReal.ofReal of the optimum; reason: attainment and finiteness written out
--   - encoding: “if f is a decision problem” (Ω = {0,1}) → a second clause for every g : Σ → Bool on the same Σ and μ; reason: Bool is {0,1}; the decision clause is stated for all decision problems on the same data
-- source:
--   Ben-David, Ebtehaj, Distributional Quantum Query Complexity, arXiv:2610.06835 (held version, sha256 6334ffaf…), Proposition 6.3, pp.47–48

import Mathlib
import Definitions.Def_DistQuantumQuery_rAdv

open scoped Matrix ENNReal ComplexOrder Topology

namespace DistQuantumQuery

/-- **Proposition 6.3** (Ben-David, Ebtehaj, *Distributional Quantum Query Complexity*, arXiv:2610.06835,
held version, sha256 6334ffaf…, Proposition 6.3, pp.47–48). Let `Σ ⊆ {0,1}^n`, `f : Σ → Ω`
functional, `μ` a distribution and `δ ∈ [0,1]`. Then
`rAdv^μ_δ(f) = max_{Γ = Γ†, Γ ∘ I = 0, max_i ‖Γ ∘ Δ_i‖ ≤ 1} min_{Ψ ∈ R^μ_δ(f)} ⟨Γ, (J − Ψ) ∘ |μ⟩⟨μ|⟩`.
Moreover, if `f` is a decision problem, then
`rAdv^μ_δ(f) = max_{Γ = Γ†, Γ ∘ Δ_f = Γ, max_i ‖Γ ∘ Δ_i‖ ≤ 1} ⟨Γ, Δ_f ∘ |μ⟩⟨μ|⟩ − δ‖Γ‖`.
In particular, the value is finite and both maxima are attained.

**Formalization Note** As in Lemma 5.2: a real `v` with `rAdv = ofReal v`, inner minima attained
for every feasible `Γ`, `v` the greatest; the decision clause is stated for every `g : Σ → Bool`
on the same `Σ, μ, δ`. Objectives are real parts. -/
theorem proposition_6_3 {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω] [DecidableEq Ω]
    (S : Finset (ι → Bool)) (f : S → Ω) (μ : S → ℝ) (hμ : IsDist μ) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1) :
    let feas : Matrix S S ℂ → Prop := fun Γ => Γ.IsHermitian ∧ Γ ⊙ (1 : Matrix S S ℂ) = 0 ∧
      ∀ i, opNorm (Γ ⊙ qfilters S i) ≤ 1
    let obj : Matrix S S ℂ → Matrix S S ℂ → ℝ := fun Γ Ψ =>
      (hsInner Γ ((allOnes S - Ψ) ⊙ muMat μ)).re
    ((∀ Γ, feas Γ → ∃ w, IsLeast (obj Γ '' relaxedTargets μ f δ) w) ∧
      ∃ v : ℝ, rAdv S μ f δ = ENNReal.ofReal v ∧
        IsGreatest {w | ∃ Γ, feas Γ ∧ IsLeast (obj Γ '' relaxedTargets μ f δ) w} v) ∧
    (∀ g : S → Bool, ∃ v : ℝ, rAdv S μ g δ = ENNReal.ofReal v ∧
      IsGreatest {w | ∃ Γ : Matrix S S ℂ, Γ.IsHermitian ∧ Γ ⊙ disagree g = Γ ∧
        (∀ i, opNorm (Γ ⊙ qfilters S i) ≤ 1) ∧
        w = (hsInner Γ (disagree g ⊙ muMat μ)).re - δ * opNorm Γ} v) := by sorry

end DistQuantumQuery
