-- Prove2me | Theorems.Thm_BwSC_LowerBound_proposition_5
-- name    : BwSC.LowerBound.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:33:17.856333+00:00
-- url     : https://prove2.me/theorems/1cf8a4a4-b63e-41ad-bf06-c17d5e795c04
-- title:
--   Proposition 5, p. 56, eq. (35) — generalized reverse Fano: (1/N)ΣP_i(E_i) ≥ q̄ − √(2 q̄ · (1/N)ΣD(P_i‖Q_i)), D = KL or reverse KL
-- statement:
--   Let $N\ge1$, let $(\Omega_1,\mathcal F_1),\dots,(\Omega_N,\mathcal F_N)$ be measurable spaces, possibly different, and for each $i\in[N]$ let $\mathbb P_i,\mathbb Q_i$ be probability measures on $(\Omega_i,\mathcal F_i)$ and $E_i\in\mathcal F_i$ an event. Put $\bar p=\frac1N\sum_i\mathbb P_i(E_i)$ and $\bar q=\frac1N\sum_i\mathbb Q_i(E_i)$. Let $D$ be either the KL divergence, $D(\mathbb P\|\mathbb Q)=\mathrm{KL}(\mathbb P\|\mathbb Q)$, or the reverse KL divergence, $D(\mathbb P\|\mathbb Q)=\mathrm{KL}(\mathbb Q\|\mathbb P)$. If every $D(\mathbb P_i\|\mathbb Q_i)$ is finite, then
--   $$\bar p\ \ge\ \bar q-\sqrt{2\,\bar q\cdot\frac1N\sum_{i=1}^N D(\mathbb P_i\,\|\,\mathbb Q_i)} .$$
--   Both choices of $D$ are stated, as two conjuncts.
--
--   The inequality lower-bounds the average probability of events under one family of measures from their average probability under another and the average divergence; it is the last step (J.5) of the proof of Theorem 2, applied with the reverse KL divergence.
--
--   **Formalization Note** Divergences are Mathlib's `klDiv`, valued in $[0,\infty]$; each conjunct assumes the divergences it uses are finite and converts them to real numbers. This loses nothing: if some divergence is infinite and $\bar q>0$ the right side is $-\infty$, and if $\bar q=0$ the right side is at most $0$. The bound (36) for $\bar q\le1/2$ is not stated.
-- source:
--   Simchi-Levi & Xu, Phase Transitions in Bandits with Switching Constraints, arXiv:1905.10825v4, p. 56, Proposition 5 (Generalized Reverse Fano-type Inequality), eq. (35)

import Mathlib

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace BwSC.LowerBound

universe u

/-- Proposition 5, p. 56, eq. (35) (generalized reverse Fano-type inequality), for both choices
of `D`: the KL divergence `D(P ∥ Q) = KL(P ∥ Q)` and the reverse KL divergence
`D(P ∥ Q) = KL(Q ∥ P)`. With `p̄ = (1/N) Σ P_i(E_i)`, `q̄ = (1/N) Σ Q_i(E_i)` and
`D̄ = (1/N) Σ D(P_i ∥ Q_i)` (all finite): `p̄ ≥ q̄ - √(2 q̄ D̄)`. -/
theorem proposition_5 {N : ℕ} (hN : 0 < N) {Ω : Fin N → Type u}
    [∀ i, MeasurableSpace (Ω i)] (P Q : ∀ i, Measure (Ω i))
    [∀ i, IsProbabilityMeasure (P i)] [∀ i, IsProbabilityMeasure (Q i)]
    (E : ∀ i, Set (Ω i)) (hE : ∀ i, MeasurableSet (E i)) :
    ((∀ i, klDiv (P i) (Q i) ≠ ∞) →
      (1 / (N : ℝ)) * ∑ i, (Q i (E i)).toReal -
          Real.sqrt (2 * ((1 / (N : ℝ)) * ∑ i, (Q i (E i)).toReal) *
            ((1 / (N : ℝ)) * ∑ i, (klDiv (P i) (Q i)).toReal))
        ≤ (1 / (N : ℝ)) * ∑ i, (P i (E i)).toReal) ∧
    ((∀ i, klDiv (Q i) (P i) ≠ ∞) →
      (1 / (N : ℝ)) * ∑ i, (Q i (E i)).toReal -
          Real.sqrt (2 * ((1 / (N : ℝ)) * ∑ i, (Q i (E i)).toReal) *
            ((1 / (N : ℝ)) * ∑ i, (klDiv (Q i) (P i)).toReal))
        ≤ (1 / (N : ℝ)) * ∑ i, (P i (E i)).toReal) := by sorry

end BwSC.LowerBound
