-- Prove2me | Theorems.Thm_BurkholderDFI_Brownian_eq_8_1
-- name    : BurkholderDFI.Brownian.eq_8_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:13:16.365144+00:00
-- url     : https://prove2.me/theorems/5facdf35-6f95-4668-b0b8-a91ea3f0d830
-- title:
--   (8.1) — Wald's identity $EX^2(\tau)=E\tau$ for a bounded stopping time of Brownian motion
-- statement:
--   Let $X$ be a one-dimensional Brownian motion with continuous sample functions on a probability space $(\Omega,\mathcal A,P)$, $\mathcal B(t)$ its natural $\sigma$-fields, and $\tau$ a stopping time of $X$ ($\{\tau<t\}\in\mathcal B(t)$ for $t>0$) that is bounded: $\tau\le T$ for a finite constant $T$. Then
--   $$EX^2(\tau)=E\tau .$$
--
--   The paper cites this identity as well known, a consequence of Doob's optional sampling theorem applied to the martingale $\{X^2(t)-t,\ t\ge0\}$. It is the one fact about Brownian motion beyond path continuity that the proof of Theorem 6.2 uses.
--
--   **Formalization Note** Both expectations are integrals of nonnegative functions in $[0,\infty]$ (`lintegral`), so neither side can take a junk value; since $\tau\le T$, both sides are finite. $X(\tau)$ is $X$ evaluated at the finite time $\tau(\omega)$.
-- source:
--   Burkholder, Distribution Function Inequalities for Martingales, Ann. Probability 1 (1973), §8, proof of Theorem 6.2, (8.1), p. 27 (cited from Doob, Stochastic Processes, p. 380)

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale
import Definitions.Def_BurkholderDFI_Brownian_Process
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace BurkholderDFI.Brownian

/-- (8.1), §8, p. 27: Wald's identity `E X²(τ) = E τ` for a bounded stopping time `τ` of
Brownian motion (cited by the paper from Doob [15], p. 380). -/
theorem eq_8_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (hX : IsBM X P) (τ : Ω → ℝ≥0∞) (hτ : IsStoppingTimeOf X τ)
    (T : ℝ≥0) (hT : ∀ ω, τ ω ≤ T) :
    ∫⁻ ω, ENNReal.ofReal (X (τ ω).toNNReal ω ^ 2) ∂P = ∫⁻ ω, τ ω ∂P := by sorry

end BurkholderDFI.Brownian
