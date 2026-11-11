-- Prove2me | Theorems.Thm_DistQuantumQuery_lemma_6_7
-- name    : DistQuantumQuery.lemma_6_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:19:20.383424+00:00
-- url     : https://prove2.me/theorems/5a1529ab-0ea6-4ef0-85f8-23def7488b40
-- title:
--   Lemma 6.7 — PSD repair of a relaxed target into Gram matrices $\hat J,\hat\Psi$
-- statement:
--   Let $\Sigma\subseteq\{0,1\}^n$, $f:\Sigma\to\Omega$ functional, $\mu$ a distribution and $\delta\in[0,1]$. Let $\Psi\in\mathrm{Herm}(\Sigma)$ satisfy $\Psi\circ A_f=A_f$ and $\|\Psi\circ\Delta_f\circ|\mu\rangle\langle\mu|\|_{\mathrm{tr}}\le\delta$. Then there are Gram matrices $\hat J,\hat\Psi$ such that
--
--   1. $\hat J\circ I=I$ and $\hat\Psi\circ I=I$;
--   2. $F(\hat J\circ|\mu\rangle\langle\mu|,J\circ|\mu\rangle\langle\mu|)\ge\dfrac1{\sqrt{1+\delta/2}}$ and $F(\hat\Psi\circ|\mu\rangle\langle\mu|,A_f\circ|\mu\rangle\langle\mu|)\ge\dfrac1{\sqrt{1+\delta/2}}$;
--   3. $\bar\gamma^\mu_2(\hat J-\hat\Psi\mid\{\Delta_i\})\le\bar\gamma^\mu_2(J-\Psi\mid\{\Delta_i\})$.
--
--   This turns a relaxed (Hermitian) certificate into a pair of Gram matrices to which state conversion applies (Proposition 6.6).
--
--   **Formalization Note** A Gram matrix is a positive semidefinite matrix.
--
--   Differences from the source:
--   - encoding: Σ ⊂ {0,1}^n with positions [n] → Σ a Finset of bit strings ι → Bool over a finite type ι of positions; reason: relabelling positions; ι = Fin n is the source's case and every finite ι is a relabelling of some Fin n
--   - encoding: min / max / inf of measures, +∞ if unbounded; Q an integer → values in ℝ≥0∞ (Q in ℕ∞, cast to ℝ≥0∞); min/inf as ⨅, max/sup as ⨆; reason: same values, with ⊤ for +∞; no real cast that would send ⊤ to 0
-- source:
--   Ben-David, Ebtehaj, Distributional Quantum Query Complexity, arXiv:2610.06835 (held version, sha256 6334ffaf…), Lemma 6.7, p.50

import Mathlib
import Definitions.Def_DistQuantumQuery_rAdv

open scoped Matrix ENNReal ComplexOrder Topology

namespace DistQuantumQuery

/-- **Lemma 6.7 (PSD repair lemma)** (Ben-David, Ebtehaj, *Distributional Quantum Query Complexity*, arXiv:2610.06835,
held version, sha256 6334ffaf…, Lemma 6.7, p.50). Let `Σ ⊆ {0,1}^n`, `f : Σ → Ω`
functional, `μ` a distribution and `δ ∈ [0,1]`. Let `Ψ ∈ Herm(Σ)` satisfy `Ψ ∘ A_f = A_f` and
`‖Ψ ∘ Δ_f ∘ |μ⟩⟨μ|‖_tr ≤ δ`. Then there are Gram matrices `Ĵ, Ψ̂` with
(i) `Ĵ ∘ I = I` and `Ψ̂ ∘ I = I`;
(ii) `F(Ĵ ∘ |μ⟩⟨μ|, J ∘ |μ⟩⟨μ|) ≥ 1/√(1+δ/2)` and `F(Ψ̂ ∘ |μ⟩⟨μ|, A_f ∘ |μ⟩⟨μ|) ≥ 1/√(1+δ/2)`;
(iii) `γ̄^μ₂(Ĵ − Ψ̂ | {Δ_i}) ≤ γ̄^μ₂(J − Ψ | {Δ_i})`. -/
theorem lemma_6_7 {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω] [DecidableEq Ω]
    (S : Finset (ι → Bool)) (f : S → Ω) (μ : S → ℝ) (hμ : IsDist μ) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1) (Ψ : Matrix S S ℂ) (hΨ : Ψ.IsHermitian) (hΨa : Ψ ⊙ agree f = agree f)
    (hΨt : traceNorm (Ψ ⊙ disagree f ⊙ muMat μ) ≤ δ) :
    ∃ Jh Ψh : Matrix S S ℂ, Jh.PosSemidef ∧ Ψh.PosSemidef ∧
      Jh ⊙ (1 : Matrix S S ℂ) = 1 ∧ Ψh ⊙ (1 : Matrix S S ℂ) = 1 ∧
      1 / Real.sqrt (1 + δ / 2) ≤ fidelity (Jh ⊙ muMat μ) (allOnes S ⊙ muMat μ) ∧
      1 / Real.sqrt (1 + δ / 2) ≤ fidelity (Ψh ⊙ muMat μ) (agree f ⊙ muMat μ) ∧
      gammaBar μ (Jh - Ψh) (qfilters S) ≤ gammaBar μ (allOnes S - Ψ) (qfilters S) := by sorry

end DistQuantumQuery
