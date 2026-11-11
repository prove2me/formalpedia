-- Prove2me | Theorems.Thm_DistQuantumQuery_lemma_4_5
-- name    : DistQuantumQuery.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:15:59.9802+00:00
-- url     : https://prove2.me/theorems/5ec45d74-8002-43ab-b0ba-18f918059368
-- title:
--   Lemma 4.5 — equivalent forms of $\bar\gamma^\mu_2(B\mid\{\Delta_i\})$ for query filters
-- statement:
--   Let $\Sigma\subseteq\{0,1\}^n$ and $B\in\mathrm{Herm}(\Sigma)$ with $B\circ I=0$. Let
--   $$
--   L:=\{\Gamma\in\mathrm{Herm}(\Sigma):\ \Gamma\circ I=0,\ \|\Gamma\circ\Delta_i\|\le1\ \forall i\in[n]\}.
--   $$
--   Then $L$ is compact and convex, and for every distribution $\mu$ on $\Sigma$,
--   $$
--   \bar\gamma^\mu_2(B\mid\{\Delta_i\})=\max_{\Gamma\in L}\langle\Gamma,B\circ|\mu\rangle\langle\mu|\rangle .
--   $$
--   Moreover, $(B,\mu)\mapsto\bar\gamma^\mu_2(B\mid\{\Delta_i\})$ is jointly continuous on Hermitian $B$ with $B\circ I=0$ and distributions $\mu$. Consequently
--   $$
--   \bar\gamma^\mu_2(B\mid\{\Delta_i\})=\max_{\Gamma\ne0,\ \Gamma=\Gamma^\dagger,\ \Gamma\circ I=0}\frac{\langle\Gamma,B\circ|\mu\rangle\langle\mu|\rangle}{\max_i\|\Gamma\circ\Delta_i\|}.
--   $$
--   In particular, the value is finite and both maxima are attained.
--
--   **Formalization Note** Continuity is in the topology of $[0,\infty]$ on the set of pairs $(B,\mu)$ described. The quotient form is stated under $|\Sigma|\ge2$ (footnote 6, p.39).
--
--   Differences from the source:
--   - encoding: Σ ⊂ {0,1}^n with positions [n] → Σ a Finset of bit strings ι → Bool over a finite type ι of positions; reason: relabelling positions; ι = Fin n is the source's case and every finite ι is a relabelling of some Fin n
--   - encoding: min / max / inf of measures, +∞ if unbounded; Q an integer → values in ℝ≥0∞ (Q in ℕ∞, cast to ℝ≥0∞); min/inf as ⨅, max/sup as ⨆; reason: same values, with ⊤ for +∞; no real cast that would send ⊤ to 0
--   - encoding: the real number ⟨Γ, M⟩ for Hermitian Γ and Hermitian M (or Tr of a PSD matrix) → the real part of ⟨Γ, M⟩ (resp. of the trace); reason: the inner product is real under the stated hypotheses
--   - encoding: “max”/“min” attained; “the value is finite” → IsGreatest / IsLeast of the real objective sets, and the measure equals ENNReal.ofReal of the optimum; reason: attainment and finiteness written out
--   - encoding: quotient form, under the paper-wide implicit assumption |Σ| ≥ 2 (footnote 6) → the quotient form carries the hypothesis 2 ≤ |Σ|; reason: for |Σ| = 1 there is no non-zero zero-diagonal Γ and the quotient maximum is undefined; the hypothesis excludes only that case
-- source:
--   Ben-David, Ebtehaj, Distributional Quantum Query Complexity, arXiv:2610.06835 (held version, sha256 6334ffaf…), Lemma 4.5, p.39; footnote 6, p.39

import Mathlib
import Definitions.Def_DistQuantumQuery_gammaBar

open scoped Matrix ENNReal ComplexOrder Topology

namespace DistQuantumQuery

/-- **Lemma 4.5 (Equivalent forms for query filters)** (Ben-David, Ebtehaj, *Distributional Quantum Query Complexity*, arXiv:2610.06835,
held version, sha256 6334ffaf…, Lemma 4.5, p.39).
Let `Σ ⊆ {0,1}^n`, `B ∈ Herm(Σ)` with `B ∘ I = 0`, and
`L := {Γ ∈ Herm(Σ) : Γ ∘ I = 0, ‖Γ ∘ Δ_i‖ ≤ 1 ∀ i}`. Then `L` is compact and convex, and for every
distribution `μ`, `γ̄^μ₂(B | {Δ_i}) = max_{Γ ∈ L} ⟨Γ, B ∘ |μ⟩⟨μ|⟩`. Moreover, `(B, μ) ↦ γ̄^μ₂(B|{Δ_i})`
is jointly continuous on Hermitian `B` with `B ∘ I = 0` and distributions `μ`. Consequently
`γ̄^μ₂(B | {Δ_i}) = max_{Γ ≠ 0, Γ = Γ†, Γ ∘ I = 0} ⟨Γ, B ∘ |μ⟩⟨μ|⟩ / max_i ‖Γ ∘ Δ_i‖`. In particular, the
value is finite and both maxima are attained.

**Formalization Note** The common value is a real `v` with `γ̄₂ = ofReal v` (finiteness), the
greatest element of both objective sets (attainment). The quotient form carries `|Σ| ≥ 2`
(footnote 6, p.39: "Implicitly, we are assuming |Σ| ≥ 2 throughout the paper"); for `|Σ| = 1`
there is no non-zero zero-diagonal `Γ`. Continuity is in the topology of `ℝ≥0∞`, on the set of
pairs `(B, μ)` with `B` Hermitian, `B ∘ I = 0` and `μ` a distribution. -/
theorem lemma_4_5 {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Finset (ι → Bool))
    (B : Matrix S S ℂ) (hB : B.IsHermitian) (hBd : B ⊙ (1 : Matrix S S ℂ) = 0) :
    let L : Set (Matrix S S ℂ) := {Γ | Γ.IsHermitian ∧ Γ ⊙ (1 : Matrix S S ℂ) = 0 ∧
      ∀ i, opNorm (Γ ⊙ qfilters S i) ≤ 1}
    IsCompact L ∧ Convex ℝ L ∧
    (∀ μ : S → ℝ, IsDist μ → ∃ v : ℝ,
      IsGreatest ((fun Γ => (hsInner Γ (B ⊙ muMat μ)).re) '' L) v ∧
      gammaBar μ B (qfilters S) = ENNReal.ofReal v ∧
      (2 ≤ S.card → IsGreatest {w | ∃ Γ : Matrix S S ℂ, Γ ≠ 0 ∧ Γ.IsHermitian ∧
        Γ ⊙ (1 : Matrix S S ℂ) = 0 ∧
        w = (hsInner Γ (B ⊙ muMat μ)).re / maxFilterNorm Γ (qfilters S)} v)) ∧
    ContinuousOn (fun p : Matrix S S ℂ × (S → ℝ) => gammaBar p.2 p.1 (qfilters S))
      {p | p.1.IsHermitian ∧ p.1 ⊙ (1 : Matrix S S ℂ) = 0 ∧ IsDist p.2} := by sorry

end DistQuantumQuery
