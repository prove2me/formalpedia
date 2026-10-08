-- Prove2me | Theorems.Thm_BurkholderDFI_ConcavePhi_stopped_sum_identity
-- name    : BurkholderDFI.ConcavePhi.stopped_sum_identity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:16:07.47685+00:00
-- url     : https://prove2.me/theorems/9102cb69-e3a4-4c12-a3dd-556d2dae9cb5
-- title:
--   §20, proof of Theorem 20.1 — EZ_τ = EW_τ ≤ E(W ∧ λ) and E[λI(τ < ∞)] = λP(W > λ) ≤ E(W ∧ λ)
-- statement:
--   Let $(\Omega,\mathcal A,P)$ be a probability space with sub-$\sigma$-fields $\mathcal A_0\subseteq\mathcal A_1\subseteq\cdots$ of $\mathcal A$, and let $z_1,z_2,\dots$ be nonnegative ($[0,\infty]$-valued) measurable functions on $\Omega$. Write $Z_n=\sum_{k=1}^n z_k$ and $W_n=\sum_{k=1}^n E(z_k\mid\mathcal A_{k-1})$ for $0\le n\le\infty$, $Z=Z_\infty$, $W=W_\infty$, and for $\lambda>0$ let $\tau=\inf\{n\ge0:W_{n+1}>\lambda\}$ (with $\inf\emptyset=\infty$). Then, everywhere on $\Omega$,
--
--   $$Z\wedge\lambda\le Z_\tau+\lambda I(\tau<\infty),$$
--
--   and
--
--   $$EZ_\tau=E\sum_{k=1}^\infty I(\tau\ge k)z_k=E\sum_{k=1}^\infty I(\tau\ge k)E(z_k\mid\mathcal A_{k-1})=EW_\tau\le E(W\wedge\lambda)$$
--
--   and
--
--   $$E[\lambda I(\tau<\infty)]=\lambda P(W>\lambda)\le E(W\wedge\lambda).$$
--
--   Together, these three displays give the truncated inequality (20.2).
--
--   **Formalization Note** The statement has five conjuncts: the pointwise bound $Z\wedge\lambda\le Z_\tau+\lambda I(\tau<\infty)$; $EZ_\tau=EW_\tau$; $EW_\tau\le E(W\wedge\lambda)$; $E[\lambda I(\tau<\infty)]=\lambda P(W>\lambda)$; $\lambda P(W>\lambda)\le E(W\wedge\lambda)$. All expectations are Lebesgue integrals of $[0,\infty]$-valued functions and the conditional expectations are `condLExp`, so no integrability is assumed. $\lambda$ is a positive real (`l : ℝ≥0`, `0 < l`). The $z_k$ are measurable for $\mathcal A$; they are not assumed adapted.
-- source:
--   Burkholder, Distribution Function Inequalities for Martingales, Ann. Probability 1 (1973), §20, proof of Theorem 20.1, p. 38

import Mathlib
import Definitions.Def_BurkholderDFI_ConcavePhi_Partial

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace BurkholderDFI.ConcavePhi

/-- §20, proof of Theorem 20.1, p. 38: with `τ = inf {n ≥ 0 : W_{n+1} > λ}`,
`Z ∧ λ ≤ Z_τ + λI(τ < ∞)` pointwise,
`EZ_τ = E Σ I(τ ≥ k) z_k = E Σ I(τ ≥ k) E(z_k|𝒜_{k−1}) = EW_τ ≤ E(W ∧ λ)` and
`E[λ I(τ < ∞)] = λ P(W > λ) ≤ E(W ∧ λ)`. -/
theorem stopped_sum_identity {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ mΩ)
    (z : ℕ → Ω → ℝ≥0∞) (hz : ∀ k, Measurable (z k)) (l : ℝ≥0) (hl : 0 < l) :
    (∀ ω, min (Zpart z ⊤ ω) (l : ℝ≥0∞) ≤ Zpart z (stopIdx ℱ P z l ω) ω
        + Set.indicator {ω | stopIdx ℱ P z l ω < ⊤} (fun _ => (l : ℝ≥0∞)) ω) ∧
    (∫⁻ ω, Zpart z (stopIdx ℱ P z l ω) ω ∂P = ∫⁻ ω, Wpart ℱ P z (stopIdx ℱ P z l ω) ω ∂P) ∧
    (∫⁻ ω, Wpart ℱ P z (stopIdx ℱ P z l ω) ω ∂P ≤ ∫⁻ ω, min (Wpart ℱ P z ⊤ ω) (l : ℝ≥0∞) ∂P) ∧
    (∫⁻ ω, Set.indicator {ω | stopIdx ℱ P z l ω < ⊤} (fun _ => (l : ℝ≥0∞)) ω ∂P
        = (l : ℝ≥0∞) * P {ω | (l : ℝ≥0∞) < Wpart ℱ P z ⊤ ω}) ∧
    ((l : ℝ≥0∞) * P {ω | (l : ℝ≥0∞) < Wpart ℱ P z ⊤ ω}
        ≤ ∫⁻ ω, min (Wpart ℱ P z ⊤ ω) (l : ℝ≥0∞) ∂P) := by sorry

end BurkholderDFI.ConcavePhi
