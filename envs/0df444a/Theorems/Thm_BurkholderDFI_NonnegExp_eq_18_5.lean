-- Prove2me | Theorems.Thm_BurkholderDFI_NonnegExp_eq_18_5
-- name    : BurkholderDFI.NonnegExp.eq_18_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:12:30.561461+00:00
-- url     : https://prove2.me/theorems/86eb8a78-b4a6-47f6-a495-a59f039672ed
-- title:
--   (18.5) — the stopped square-function tail beyond a shifted threshold
-- statement:
--   Let $f$ be a nonnegative martingale, let $\lambda>0$, and set $\mu=\inf\{n\ge1:|f_n|>\lambda\}$. For every $a>0$,
--
--   $$
--   \int_{a+\lambda^2}^{\infty}
--     P\bigl(S_{\mu-1}(f)^2>s\bigr)\,ds
--     \le 2\lambda^2 P\bigl(S_{\mu-1}(f)^2>a\bigr).
--   $$
--
--   This is the outer inequality of display (18.5). It isolates the tail estimate later combined with the preceding interval.
--
--   **Formalization Note** The paper's stopping time $\nu$ appears in the intervening proof equalities, not in this outer inequality. The square function and integral are extended nonnegative, so infinite values are represented honestly. Nonnegativity is asserted almost everywhere at every positive time, and Mathlib's index $0$ is auxiliary.
-- source:
--   Burkholder, Distribution Function Inequalities for Martingales, Ann. Probability 1 (1973), (18.5), proof of Theorem 18.1, p. 37; https://doi.org/10.1214/aop/1176997023

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

namespace BurkholderDFI.NonnegExp
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

/-- (18.5), p. 37: the tail integral after the stopping threshold. -/
theorem eq_18_5 {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ P) (hnn : ∀ n, 1 ≤ n → 0 ≤ᵐ[P] f n)
    (l : ℝ) (hl : 0 < l) (a : ℝ) (ha : 0 < a) :
    ∫⁻ s in Set.Ioi (a + l ^ 2), P {ω | ENNReal.ofReal s < BurkholderDFI.SquareFnLp.sqFnAt f (BurkholderDFI.SquareFnLp.exitTime f l ω - 1) ω ^ 2}
      ≤ ENNReal.ofReal (2 * l ^ 2) * P {ω | ENNReal.ofReal a < BurkholderDFI.SquareFnLp.sqFnAt f (BurkholderDFI.SquareFnLp.exitTime f l ω - 1) ω ^ 2} := by sorry

end BurkholderDFI.NonnegExp
