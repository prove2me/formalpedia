-- Prove2me | Theorems.Thm_DynColorWC_Main_lemma_3_4
-- name    : DynColorWC.Main.lemma_3_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:46:07.683112+00:00
-- url     : https://prove2.me/theorems/82193432-fda6-4194-9710-91c9eb3d7029
-- title:
--   Lemma 3.4 — Chernoff upper and lower tails for independent [0,1]-valued variables
-- statement:
--   Let $X_1,\dots,X_n\in[0,1]$ be mutually independent random variables and $X=\sum_iX_i$. Then for all $\delta>0$,
--   $$\Pr[X\ge(1+\delta)\mathbb E[X]]\le\exp\Big(-\frac{\delta^2\mathbb E[X]}{2(1+\delta)}\Big),$$
--   and for all $\delta\in[0,1]$, $\Pr[X\le(1-\delta)\mathbb E[X]]\le\exp(-\delta^2\mathbb E[X]/2)$.
--
--   Differences from the source:
--
--   - encoding: mutually independent X_1, …, X_n ∈ [0, 1] with E[X] → measurable X : Fin n → Ω → ℝ, iIndepFun under a probability measure, 0 ≤ X_i ω ≤ 1 at every ω; E[X] is the Bochner integral of Σ X_i and P is μ.real; reason: bounded measurable variables are integrable, so E[X] is genuine
-- source:
--   Flin and Ghaffari (2026), Dynamic (Δ+1)-Coloring with Polylogarithmic Worst-Case Update Time, STOC 2027 submission, supplied PDF sha256 93ebb2ffd4839b5e525b4550a6569cf5234550ee4a44351aedab3ea3154300e3, Lemma 3.4, p. 14 (PDF 16)

import Mathlib

namespace DynColorWC.Main

open MeasureTheory ProbabilityTheory

/-- **Lemma 3.4** (Chernoff bound; Flin and Ghaffari (2026), STOC 2027 submission,
sha256 93ebb2ff…3154300e3, p. 14 (PDF 16)). Let `X_1, …, X_n ∈ [0, 1]` be mutually independent random
variables and `X = Σ_i X_i`. Then for all `δ > 0`,
`P[X ≥ (1 + δ) E[X]] ≤ exp(−δ² E[X] / (2(1 + δ)))`, and for all `δ ∈ [0, 1]`,
`P[X ≤ (1 − δ) E[X]] ≤ exp(−δ² E[X] / 2)`. -/
theorem lemma_3_4 {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ)
    (X : Fin n → Ω → ℝ) (hmeas : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hrange : ∀ i ω, 0 ≤ X i ω ∧ X i ω ≤ 1) :
    (∀ δ : ℝ, 0 < δ →
      μ.real {ω | (1 + δ) * (∫ ω', ∑ i, X i ω' ∂μ) ≤ ∑ i, X i ω} ≤
        Real.exp (-(δ ^ 2 * (∫ ω', ∑ i, X i ω' ∂μ)) / (2 * (1 + δ)))) ∧
    (∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
      μ.real {ω | ∑ i, X i ω ≤ (1 - δ) * (∫ ω', ∑ i, X i ω' ∂μ)} ≤
        Real.exp (-(δ ^ 2 * (∫ ω', ∑ i, X i ω' ∂μ)) / 2)) := by sorry

end DynColorWC.Main
