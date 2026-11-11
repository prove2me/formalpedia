-- Prove2me | Theorems.Thm_DistQuantumQuery_lemma_5_2
-- name    : DistQuantumQuery.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:17:36.251189+00:00
-- url     : https://prove2.me/theorems/18fd505c-8589-47e8-a359-2c4f047f6214
-- title:
--   Lemma 5.2 — minimax form $\mathrm{Adv}^\mu_\varepsilon(f)=\max_\Gamma\min_{\Psi\in\mathcal G^\mu_\varepsilon(f)}\langle\Gamma,(J-\Psi)\circ|\mu\rangle\langle\mu|\rangle$
-- statement:
--   Let $\Sigma\subseteq\{0,1\}^n$, $f\subseteq\Sigma\times\Omega$ a search problem, $\mu$ a distribution and $\varepsilon\in[0,1)$. Then
--   $$
--   \mathrm{Adv}^\mu_\varepsilon(f)=\max_{\Gamma=\Gamma^\dagger,\ \max_i\|\Gamma\circ\Delta_i\|\le1}\ \min_{\Psi\in\mathcal G^\mu_\varepsilon(f)}\langle\Gamma,(J-\Psi)\circ|\mu\rangle\langle\mu|\rangle .
--   $$
--   Moreover, one may assume $\Gamma\circ I=0$. In particular, the value is finite and both the maximum and the inner minimum are attained.
--
--   A single adversary matrix $\Gamma$ thus certifies a lower bound against every target; this is what the composition proof lifts.
--
--   **Formalization Note** For every feasible $\Gamma$ the inner minimum is attained; the optimum $v$ is the greatest inner minimum, $\mathrm{Adv}=v$, and $v$ is attained by a feasible $\Gamma$ with zero diagonal.
--
--   Differences from the source:
--   - encoding: Σ ⊂ {0,1}^n with positions [n] → Σ a Finset of bit strings ι → Bool over a finite type ι of positions; reason: relabelling positions; ι = Fin n is the source's case and every finite ι is a relabelling of some Fin n
--   - encoding: min / max / inf of measures, +∞ if unbounded; Q an integer → values in ℝ≥0∞ (Q in ℕ∞, cast to ℝ≥0∞); min/inf as ⨅, max/sup as ⨆; reason: same values, with ⊤ for +∞; no real cast that would send ⊤ to 0
--   - encoding: the real number ⟨Γ, M⟩ for Hermitian Γ and Hermitian M (or Tr of a PSD matrix) → the real part of ⟨Γ, M⟩ (resp. of the trace); reason: the inner product is real under the stated hypotheses
--   - encoding: “max”/“min” attained; “the value is finite” → IsGreatest / IsLeast of the real objective sets, and the measure equals ENNReal.ofReal of the optimum; reason: attainment and finiteness written out
--   - encoding: G^μ_ε(f): max_{W ∈ W^μ_f} F(W ∘ |μ⟩⟨μ|, Ψ ∘ |μ⟩⟨μ|) ≥ √(1−ε) → ∃ W ∈ W^μ_f with F ≥ √(1−ε); reason: the source writes max, i.e. the maximum is attained
-- source:
--   Ben-David, Ebtehaj, Distributional Quantum Query Complexity, arXiv:2610.06835 (held version, sha256 6334ffaf…), Lemma 5.2, p.43

import Mathlib
import Definitions.Def_DistQuantumQuery_Adv

open scoped Matrix ENNReal ComplexOrder Topology

namespace DistQuantumQuery

/-- **Lemma 5.2** (Ben-David, Ebtehaj, *Distributional Quantum Query Complexity*, arXiv:2610.06835,
held version, sha256 6334ffaf…, Lemma 5.2, p.43). Let `Σ ⊆ {0,1}^n`, `f ⊆ Σ × Ω` a search problem, `μ` a
distribution and `ε ∈ [0,1)`. Then
`Adv^μ_ε(f) = max_{Γ = Γ†, max_i ‖Γ ∘ Δ_i‖ ≤ 1} min_{Ψ ∈ G^μ_ε(f)} ⟨Γ, (J − Ψ) ∘ |μ⟩⟨μ|⟩`.
Moreover, we may assume without loss of generality that `Γ ∘ I = 0`. In particular, the value
is finite and both the maximum and the inner minimum are attained.

**Formalization Note** The value is a real `v` with `Adv = ofReal v`; for every feasible `Γ` the
inner minimum is attained (`IsLeast`), `v` is the greatest inner minimum, and it is attained by
a feasible `Γ` with `Γ ∘ I = 0`. The objective is real for Hermitian `Γ`, PSD `Ψ`; its real
part is used. The search problem is a total relation `R`. -/
theorem lemma_5_2 {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω] [DecidableEq Ω]
    (S : Finset (ι → Bool)) (R : S → Ω → Prop) (hR : ∀ x, ∃ s, R x s)
    (μ : S → ℝ) (hμ : IsDist μ) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    let feas : Matrix S S ℂ → Prop := fun Γ => Γ.IsHermitian ∧
      ∀ i, opNorm (Γ ⊙ qfilters S i) ≤ 1
    let obj : Matrix S S ℂ → Matrix S S ℂ → ℝ := fun Γ Ψ =>
      (hsInner Γ ((allOnes S - Ψ) ⊙ muMat μ)).re
    (∀ Γ, feas Γ → ∃ w, IsLeast (obj Γ '' Targets μ R ε) w) ∧
    ∃ v : ℝ, Adv S μ R ε = ENNReal.ofReal v ∧
      IsGreatest {w | ∃ Γ, feas Γ ∧ IsLeast (obj Γ '' Targets μ R ε) w} v ∧
      ∃ Γ, feas Γ ∧ Γ ⊙ (1 : Matrix S S ℂ) = 0 ∧ IsLeast (obj Γ '' Targets μ R ε) v := by sorry

end DistQuantumQuery
