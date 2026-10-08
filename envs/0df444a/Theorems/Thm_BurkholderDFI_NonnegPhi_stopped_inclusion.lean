-- Prove2me | Theorems.Thm_BurkholderDFI_NonnegPhi_stopped_inclusion
-- name    : BurkholderDFI.NonnegPhi.stopped_inclusion
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:12:37.382529+00:00
-- url     : https://prove2.me/theorems/83757c99-0410-402f-b421-b52662114e0b
-- title:
--   §18, proof of Theorem 18.2 — P(S(f) > βλ, f* ≤ δλ) ≤ P(S_{μ−1}(f) > βλ)
-- statement:
--   Let $f=(f_1,f_2,\dots)$ be any sequence of real random variables on a measure space $(\Omega,\mathcal A,P)$, let $\beta\in\mathbb R$, $\delta>0$, $\lambda>0$, and let
--   $$\mu=\inf\{n\ge1:|f_n|>\delta\lambda\}\qquad(\inf\emptyset=\infty).$$
--   Then
--   $$P\big(S(f)>\beta\lambda,\ f^*\le\delta\lambda\big)\le P\big(S_{\mu-1}(f)>\beta\lambda\big).$$
--
--   On the event $\{f^*\le\delta\lambda\}$ the exit time $\mu$ is infinite, so the stopped square function $S_{\mu-1}(f)$ coincides with $S(f)$ there. This is the first step of the proof of Theorem 18.2: it replaces the square function on the good set by a stopped square function to which (18.5) applies.
--
--   **Formalization Note** No martingale property is needed. $S_{\mu-1}(f)$ is $S(f)$ on $\{\mu=\infty\}$, with $\infty-1=\infty$.
-- source:
--   Burkholder, Distribution Function Inequalities for Martingales, Ann. Probability 1 (1973), §18, proof of Theorem 18.2, p. 37

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace BurkholderDFI.NonnegPhi

/-- §18, proof of Theorem 18.2, p. 37: with `μ = inf {n : |f_n| > δλ}`,
`P(S(f) > βλ, f^* ≤ δλ) ≤ P(S_{μ−1}(f) > βλ)`. -/
theorem stopped_inclusion {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (f : ℕ → Ω → ℝ)
    (β δ l : ℝ) (hδ : 0 < δ) (hl : 0 < l) :
    P {ω | ENNReal.ofReal (β * l) < BurkholderDFI.SquareFnLp.sqFn f ω ∧ BurkholderDFI.SquareFnLp.maxFn f ω ≤ ENNReal.ofReal (δ * l)}
      ≤ P {ω | ENNReal.ofReal (β * l) < BurkholderDFI.SquareFnLp.sqFnAt f (BurkholderDFI.SquareFnLp.exitTime f (δ * l) ω - 1) ω} := by sorry

end BurkholderDFI.NonnegPhi
