-- Prove2me | Theorems.Thm_CalibratedMA_Randomized_lemma_3_3
-- name    : CalibratedMA.Randomized.lemma_3_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-10T21:25:34.117202+00:00
-- url     : https://prove2.me/theorems/63cf65ac-aa13-426f-ae13-8caa85c8bf87
-- title:
--   Lemma 3.3 — rounding error as total variation
-- statement:
--   Let $\Gamma=(\gamma_0,\dots,\gamma_M)$ be a grid partition, $\nu$ a distribution on $[0,1]$, $S\sim\nu$ and $P=\mathrm{Round}_\Gamma(S)$. Write $q_j=q_j(\nu,\Gamma)$ for $0\le j\le M-1$ and set $q_{-1}=q_M=0$. Then
--   $$\mathrm{RoundErr}(\nu,\Gamma)=\sup_{h:\{\gamma_0,\dots,\gamma_M\}\to[-1,1]}\big|\mathbb E[h(P)(S-P)]\big|=q_0+q_{M-1}+\sum_{j=1}^{M-1}|q_j-q_{j-1}|=\sum_{j=0}^{M}|q_j-q_{j-1}|.$$
--
--   So the largest calibration residual that rounding can create is the total variation of the sequence of interval contributions $(q_j)$. Lemma 3.4 chooses the partition to make this small.
--
--   **Formalization Note.** The expectation $\mathbb E[h(P)(S-P)]$ is the iterated integral $\int\!\int h(p)(s-p)\,\mathrm{Round}_\Gamma(s)(dp)\,\nu(ds)$. The supremum is stated with `IsLUB` over all $h:\mathbb R\to\mathbb R$ whose values at the partition points lie in $[-1,1]$; only those values enter. The boundary conventions $q_{-1}=q_M=0$ are built into the auxiliary sequences `q` and `qprev`.
--
--   Differences from the source:
--   - encoding: $\sup_h|\cdot|$ over $h:\{\gamma_0,\dots,\gamma_M\}\to[-1,1]$ → `IsLUB` of the set of values $|\mathbb E[h(P)(S-P)]|$ over $h:\mathbb R\to\mathbb R$ with $h(\gamma_j)\in[-1,1]$; reason: only the values at partition points enter, and `IsLUB` is the supremum without junk values.
--   - encoding: $\rho>0$ with $1/\rho$ an integer → $K\in\mathbb N$, $\rho=1/K$; reason: same instances.
--   - encoding: the joint expectation for S ∼ ν and P = Round_Γ(S) → an iterated integral under a probability measure ν on ℝ carried by [0,1] and roundMeasure; reason: the rounding law has finite support and is measurable, so the iterated integral is the source expectation.
-- source:
--   Jiuyao Lu, Georgy Noarov, Aaron Roth, Calibrated Multiaccuracy: Deterministic and Randomized Sample Complexity, STOC 2027 submission #900 (October 2026), p. 14, Lemma 3.3

import Mathlib
import Definitions.Def_CalibratedMA_Randomized_Rounding

open MeasureTheory

namespace CalibratedMA.Randomized

/-- Lemma 3.3 (p. 14), rounding error as total variation. `S ∼ ν` with `ν` a distribution on
`[0,1]`, `P = Round_Γ(S)`, `q_j = q_j(ν, Γ)` and `q_{−1} = q_M = 0`. -/
theorem lemma_3_3 (K M : ℕ) (γ : ℕ → ℝ) (hΓ : IsGridPartition K M γ) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hν : ν (Set.Icc (0 : ℝ) 1)ᶜ = 0) :
    let q : ℕ → ℝ := fun j => if j < M then qj ν γ j else 0
    let qprev : ℕ → ℝ := fun j => if j = 0 then 0 else q (j - 1)
    IsLUB {v : ℝ | ∃ h : ℝ → ℝ, (∀ j ≤ M, h (γ j) ∈ Set.Icc (-1 : ℝ) 1) ∧
        v = |∫ s, (∫ p, h p * (s - p) ∂(roundMeasure M γ s)) ∂ν|} (RoundErr ν M γ) ∧
    RoundErr ν M γ = qj ν γ 0 + qj ν γ (M - 1) +
        ∑ j ∈ Finset.Ico 1 M, |qj ν γ j - qj ν γ (j - 1)| ∧
    RoundErr ν M γ = ∑ j ∈ Finset.range (M + 1), |q j - qprev j| := by sorry

end CalibratedMA.Randomized
