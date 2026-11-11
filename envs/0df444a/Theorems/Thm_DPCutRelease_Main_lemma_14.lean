-- Prove2me | Theorems.Thm_DPCutRelease_Main_lemma_14
-- name    : DPCutRelease.Main.lemma_14
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:12:40.16895+00:00
-- url     : https://prove2.me/theorems/3c480910-4790-4332-a234-032d5e99772f
-- title:
--   Lemma 14 — likelihood ratio of k Gaussian samples under close covariances
-- statement:
--   There is a universal constant $C>0$ with the following property. Let $\delta_1\in(0,1/2)$, let $X_0,X_1\in\mathbb R^{n\times n}$ be symmetric positive definite, $E=X_0^{-1/2}(X_1-X_0)X_1^{-1/2}$, and let $\mathrm{pdf}_0,\mathrm{pdf}_1$ be the densities of $N(0,X_0)$ and $N(0,X_1)$. Suppose $\|E\|_F<1/2$ and put
--   $$\varepsilon_1=C\Big(k\|E\|_F^2+\sqrt{k\log\tfrac1{\delta_1}}\,\|E\|_F+\log\tfrac1{\delta_1}\,\|E\|_F\Big).$$
--   Then, with probability at least $1-\delta_1$ over a batch $(Z^{(1)},\dots,Z^{(k)})$ of independent $N(0,X_0)$ vectors,
--   $$e^{-\varepsilon_1}\prod_{j=1}^k\mathrm{pdf}_1(Z^{(j)})\le\prod_{j=1}^k\mathrm{pdf}_0(Z^{(j)})\le e^{\varepsilon_1}\prod_{j=1}^k\mathrm{pdf}_1(Z^{(j)}).$$
--   It is the per-trial privacy bound of Algorithm 2.
--
--   **Formalization Note.** `batchLaw k X0` is `Measure.pi` of Mathlib's `multivariateGaussian 0 X0`; `gaussPdf X z` $=(2\pi)^{-n/2}\det(X)^{-1/2}e^{-z^\top X^{-1}z/2}$; `relErr X0 X1` is $E$ and `frobNorm` is $\|\cdot\|_F$.
--
--   Differences from the source:
--   - reading: "for ε₁ = O(k‖E‖² + √(k log(1/δ₁))‖E‖ + log(1/δ₁)‖E‖)" → ∃ universal C > 0 (before n, k, δ₁, X₀, X₁) with ε₁ = C·(…); reason: O(·) is an explicit universal constant
--   - encoding: with probability at least 1 − p → the noise/tape measure of the failure set is at most p (outer measure if the set were not measurable); reason: same statement for measurable events; cannot be made vacuous by non-measurability
-- source:
--   Eliáš et al., Polynomial-Time Differentially Private Synthetic Graph Release with Nearly-Linear Additive Error, arXiv:2611.06670v1, p. 21, Lemma 14

import Mathlib
import Definitions.Def_DPCutRelease_Main_EdgeDP
import Definitions.Def_DPCutRelease_Main_SDP

open MeasureTheory ProbabilityTheory Matrix

namespace DPCutRelease.Main

/-- Lemma 14 (p. 21): there is a universal `C` such that for `δ₁ ∈ (0, 1/2)`, symmetric positive
definite `X₀, X₁` with `E = X₀^{−1/2}(X₁ − X₀)X₁^{−1/2}`, `‖E‖_F < 1/2`, and
`ε₁ = C(k‖E‖_F² + √(k log(1/δ₁)) ‖E‖_F + log(1/δ₁) ‖E‖_F)`, the batch likelihood ratio satisfies
`e^{−ε₁} Π pdf₁ ≤ Π pdf₀ ≤ e^{ε₁} Π pdf₁` with probability at least `1 − δ₁` over `k` i.i.d.
`N(0, X₀)` vectors. -/
theorem lemma_14 :
    ∃ C : ℝ, 0 < C ∧ ∀ (n k : ℕ) (δ1 : ℝ) (X0 X1 : Mat n), 0 < δ1 → δ1 < 1 / 2 →
      X0.PosDef → X1.PosDef → frobNorm (relErr X0 X1) < 1 / 2 →
      batchLaw k X0 {Z | ¬ (Real.exp (-(C * (k * frobNorm (relErr X0 X1) ^ 2 +
              Real.sqrt (k * Real.log (1 / δ1)) * frobNorm (relErr X0 X1) +
              Real.log (1 / δ1) * frobNorm (relErr X0 X1)))) * ∏ j, gaussPdf X1 (Z j) ≤
            ∏ j, gaussPdf X0 (Z j) ∧
          ∏ j, gaussPdf X0 (Z j) ≤ Real.exp (C * (k * frobNorm (relErr X0 X1) ^ 2 +
              Real.sqrt (k * Real.log (1 / δ1)) * frobNorm (relErr X0 X1) +
              Real.log (1 / δ1) * frobNorm (relErr X0 X1))) * ∏ j, gaussPdf X1 (Z j))}
        ≤ ENNReal.ofReal δ1 := by sorry

end DPCutRelease.Main
