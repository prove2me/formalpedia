-- Prove2me | Theorems.Thm_BurkholderDFI_BMO_theorem_19_1
-- name    : BurkholderDFI.BMO.theorem_19_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:16:03.989973+00:00
-- url     : https://prove2.me/theorems/29d9e6f7-98a3-43c6-b271-78fdc2f9fed8
-- title:
--   Theorem 19.1 — exponential square integrability under condition (19.1)
-- statement:
--   Let $f=(f_n)_{n\ge1}$ be a real martingale relative to $(\mathcal A_n)$ on a probability space, with $f_0=0$ in its difference sequence $d$. Suppose that for every $n\ge1$,
--
--   $$\mathbf E\left[\sum_{k=n}^{\infty}d_k^2\,\middle|\,\mathcal A_n\right]\le1\qquad\text{almost surely}.$$
--
--   Then the square function $S(f)^2=\sum_{k=1}^{\infty}d_k^2$ is finite almost surely and, for every $0<t<1$,
--
--   $$\mathbf E\big[\exp(tS(f)^2)\big]\le(1-t)^{-1}.$$
--
--   This gives the explicit exponential square-integrability guarantee for a martingale with the normalized bounded-mean-oscillation condition (19.1).
--
--   **Formalization Note** The almost-sure finiteness clause makes the real exponential faithful when the square function is represented in $[0,\infty]$; it is a consequence, not an additional hypothesis. The conditional tail bound uses generalized conditional expectation and includes $d_n^2$ given $\mathcal A_n$. Mathlib's martingale has an index-zero extension, whereas the paper starts at index one; the difference sequence uses the paper's $f_0=0$, and any paper martingale extends to Mathlib index zero by conditional expectation.
-- source:
--   Burkholder, Distribution Function Inequalities for Martingales, Ann. Probability 1 (1973), Theorem 19.1, (19.1)–(19.2), p. 37, https://doi.org/10.1214/aop/1176997023

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale
import Definitions.Def_BurkholderDFI_BMO_Condition

namespace BurkholderDFI.BMO

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- Theorem 19.1, p. 37: (19.1) gives the sharp exponential bound (19.2). -/
theorem theorem_19_1 {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ P) (h191 : BMOCondition ℱ P f) :
    (∀ᵐ ω ∂P, BurkholderDFI.SquareFnLp.sqFn f ω ≠ ⊤) ∧
    ∀ t : ℝ, 0 < t → t < 1 →
      ∫⁻ ω, ENNReal.ofReal (Real.exp (t * ((BurkholderDFI.SquareFnLp.sqFn f ω).toReal) ^ 2)) ∂P
        ≤ ENNReal.ofReal ((1 - t)⁻¹) := by sorry

end BurkholderDFI.BMO
