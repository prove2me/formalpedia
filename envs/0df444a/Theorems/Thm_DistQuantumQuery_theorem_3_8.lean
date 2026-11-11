-- Prove2me | Theorems.Thm_DistQuantumQuery_theorem_3_8
-- name    : DistQuantumQuery.theorem_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:18:57.003396+00:00
-- url     : https://prove2.me/theorems/9871a6df-2ccd-4cef-8889-e2e121248bbb
-- title:
--   Theorem 3.8 — distributional state conversion via catalyst reuse
-- statement:
--   Let $\Sigma\subseteq\{0,1\}^n$, $\mu$ a distribution, and $\Phi,\Psi\in\mathrm{Pos}(\Sigma)$ Gram matrices with $\Phi\circ I=\Psi\circ I=I$. Suppose there are $X_1,\dots,X_n\in\mathrm{Pos}(\Sigma)$ and $r\ge1$ with
--   $$
--   \Phi-\Psi=\sum_{i=1}^n\Delta_i\circ X_i,\qquad \Psi\succeq\frac{r-1}2\sum_{i=1}^nX_i .
--   $$
--   Then for every integer $T\ge1$ there is a Gram matrix $\tilde\Psi\in\mathrm{Pos}(\Sigma)$ with $\tilde\Psi\circ I=I$ such that $Q(\Phi\to\tilde\Psi)\le T$ and, for every $W\succeq0$ with $\mathrm{Tr}(W\circ|\mu\rangle\langle\mu|)=1$,
--   $$
--   F(\tilde\Psi\circ|\mu\rangle\langle\mu|,W\circ|\mu\rangle\langle\mu|)\ \ge\ (1-\epsilon_T)\,\alpha-\sqrt{\epsilon_T(1-\alpha)},
--   $$
--   where $\alpha:=F(\Psi\circ|\mu\rangle\langle\mu|,W\circ|\mu\rangle\langle\mu|)$ and $\epsilon_T:=\sum_{i=1}^n\mathrm{Tr}(X_i\circ|\mu\rangle\langle\mu|)\big/\sum_{j=0}^{T-1}r^j$.
--
--   This is the paper's algorithmic construction; every upper bound on distributional query complexity passes through it.
--
--   **Formalization Note** One $\tilde\Psi$ serves every $W$.
--
--   Differences from the source:
--   - encoding: Σ ⊂ {0,1}^n with positions [n] → Σ a Finset of bit strings ι → Bool over a finite type ι of positions; reason: relabelling positions; ι = Fin n is the source's case and every finite ι is a relabelling of some Fin n
--   - encoding: the real number ⟨Γ, M⟩ for Hermitian Γ and Hermitian M (or Tr of a PSD matrix) → the real part of ⟨Γ, M⟩ (resp. of the trace); reason: the inner product is real under the stated hypotheses
--   - encoding: index register with basis |0⟩,…,|n⟩ and an arbitrarily large ancilla → work register Option ι × Fin (d+1), none the null index, d existential; reason: the same oracle model; Fin (d+1) always contains the start vector
--   - encoding: Q(Φ → Ψ): state families realized in a fixed, sufficiently large realization space V inside the work space → realizations existential in the algorithm's work space Option ι × Fin (d+1); reason: by Corollary 2.7 realizations with equal Gram matrices differ by an input-independent unitary, absorbed into U_0
-- source:
--   Ben-David, Ebtehaj, Distributional Quantum Query Complexity, arXiv:2610.06835 (held version, sha256 6334ffaf…), Theorem 3.8, p.29

import Mathlib
import Definitions.Def_DistQuantumQuery_Qdist
import Definitions.Def_DistQuantumQuery_traceNorm

open scoped Matrix ENNReal ComplexOrder Topology

namespace DistQuantumQuery

/-- **Theorem 3.8 (Distributional state conversion via catalyst reuse)** (Ben-David, Ebtehaj, *Distributional Quantum Query Complexity*, arXiv:2610.06835,
held version, sha256 6334ffaf…, Theorem 3.8,
p.29). Let `Σ ⊆ {0,1}^n`, `μ` a distribution, and `Φ, Ψ ∈ Pos(Σ)` Gram matrices with
`Φ ∘ I = Ψ ∘ I = I`. Suppose there exist `X_1, …, X_n ∈ Pos(Σ)` and `r ≥ 1` with
`Φ − Ψ = Σ_i Δ_i ∘ X_i` and `Ψ ⪰ ((r − 1)/2) Σ_i X_i`. Then for every integer `T ≥ 1` there is a
Gram matrix `Ψ̃ ∈ Pos(Σ)` with `Ψ̃ ∘ I = I` such that `Q(Φ → Ψ̃) ≤ T` and, for every `W ⪰ 0` with
`Tr(W ∘ |μ⟩⟨μ|) = 1`, `F(Ψ̃ ∘ |μ⟩⟨μ|, W ∘ |μ⟩⟨μ|) ≥ (1 − ε_T)α − √(ε_T(1 − α))`, where
`α := F(Ψ ∘ |μ⟩⟨μ|, W ∘ |μ⟩⟨μ|)` and `ε_T := Σ_i Tr(X_i ∘ |μ⟩⟨μ|) / Σ_{j=0}^{T−1} r^j`.

**Formalization Note** One `Ψ̃` serves every `W` (it is chosen before `W`). `Tr(X_i ∘ |μ⟩⟨μ|)` is
real for PSD `X_i`; its real part is used. -/
theorem theorem_3_8 {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Finset (ι → Bool))
    (μ : S → ℝ) (hμ : IsDist μ) (Φ Ψ : Matrix S S ℂ) (hΦ : Φ.PosSemidef) (hΨ : Ψ.PosSemidef)
    (hΦd : Φ ⊙ (1 : Matrix S S ℂ) = 1) (hΨd : Ψ ⊙ (1 : Matrix S S ℂ) = 1)
    (X : ι → Matrix S S ℂ) (hX : ∀ i, (X i).PosSemidef) (r : ℝ) (hr : 1 ≤ r)
    (hdec : Φ - Ψ = ∑ i, qfilters S i ⊙ X i)
    (hdom : (Ψ - (((r - 1) / 2 : ℝ) : ℂ) • ∑ i, X i).PosSemidef) (T : ℕ) (hT : 1 ≤ T) :
    ∃ Ψt : Matrix S S ℂ, Ψt.PosSemidef ∧ Ψt ⊙ (1 : Matrix S S ℂ) = 1 ∧
      QConv S Φ Ψt ≤ T ∧
      ∀ W : Matrix S S ℂ, W.PosSemidef → Matrix.trace (W ⊙ muMat μ) = 1 →
        (1 - (∑ i, (Matrix.trace (X i ⊙ muMat μ)).re) / ∑ j ∈ Finset.range T, r ^ j) *
              fidelity (Ψ ⊙ muMat μ) (W ⊙ muMat μ) -
            Real.sqrt ((∑ i, (Matrix.trace (X i ⊙ muMat μ)).re) / (∑ j ∈ Finset.range T, r ^ j) *
              (1 - fidelity (Ψ ⊙ muMat μ) (W ⊙ muMat μ))) ≤
          fidelity (Ψt ⊙ muMat μ) (W ⊙ muMat μ) := by sorry

end DistQuantumQuery
