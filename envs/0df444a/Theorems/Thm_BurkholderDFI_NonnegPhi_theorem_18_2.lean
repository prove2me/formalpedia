-- Prove2me | Theorems.Thm_BurkholderDFI_NonnegPhi_theorem_18_2
-- name    : BurkholderDFI.NonnegPhi.theorem_18_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:12:42.266+00:00
-- url     : https://prove2.me/theorems/91009cfb-c688-4744-a3b0-a52f977e4dac
-- title:
--   Theorem 18.2 — P(S(f) > βλ, f* ≤ δλ) ≤ 2δ²/(β² − δ² − 1)·P(S(f) > λ) for nonnegative martingales
-- statement:
--   Let $f=(f_1,f_2,\dots)$ be a nonnegative martingale on a probability space $(\Omega,\mathcal A,P)$ with respect to a filtration $(\mathcal A_n)$, with square function $S(f)=\big(\sum_{k\ge1}d_k^2\big)^{1/2}$ and maximal function $f^*=\sup_n|f_n|$. Let $\beta>1$ and $0<\delta<(\beta^2-1)^{1/2}$. Then for every $\lambda>0$,
--   $$P\big(S(f)>\beta\lambda,\ f^*\le\delta\lambda\big)\le\frac{2\delta^2}{\beta^2-\delta^2-1}\,P\big(S(f)>\lambda\big).$$
--
--   This is a **good-$\lambda$ inequality**: the event on which $S(f)$ is large while $f^*$ stays small has probability a small multiple of $P(S(f)>\lambda)$, the multiple tending to $0$ with $\delta$. Combined with Lemma 7.1 it gives Theorem 18.3. For general martingales the corresponding inequality requires a bound on the jumps $d_k$; nonnegativity removes that need.
--
--   **Formalization Note** The condition $\delta<(\beta^2-1)^{1/2}$ is stated with the real square root; together with $\delta>0$ it is equivalent to $\beta^2-\delta^2-1>0$. $S(f)$ and $f^*$ take values in $[0,\infty]$. Nonnegativity is almost sure for $n\ge1$, and the index $0$ of the Mathlib martingale is never read (any martingale relative to $\mathcal A_1,\mathcal A_2,\dots$ extends to one).
-- source:
--   Burkholder, Distribution Function Inequalities for Martingales, Ann. Probability 1 (1973), Theorem 18.2, p. 35

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace BurkholderDFI.NonnegPhi

/-- Theorem 18.2, p. 35: if `β > 1`, `0 < δ < (β² − 1)^{1/2}` and `f` is a nonnegative
martingale, then `P(S(f) > βλ, f^* ≤ δλ) ≤ 2δ²/(β² − δ² − 1) · P(S(f) > λ)` for all `λ > 0`. -/
theorem theorem_18_2 {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ P) (hnn : ∀ n, 1 ≤ n → 0 ≤ᵐ[P] f n)
    (β δ : ℝ) (hβ : 1 < β) (hδ : 0 < δ) (hδβ : δ < Real.sqrt (β ^ 2 - 1))
    (l : ℝ) (hl : 0 < l) :
    P {ω | ENNReal.ofReal (β * l) < BurkholderDFI.SquareFnLp.sqFn f ω ∧ BurkholderDFI.SquareFnLp.maxFn f ω ≤ ENNReal.ofReal (δ * l)}
      ≤ ENNReal.ofReal (2 * δ ^ 2 / (β ^ 2 - δ ^ 2 - 1)) * P {ω | ENNReal.ofReal l < BurkholderDFI.SquareFnLp.sqFn f ω} := by sorry

end BurkholderDFI.NonnegPhi
