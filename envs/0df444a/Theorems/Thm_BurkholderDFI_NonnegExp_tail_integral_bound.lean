-- Prove2me | Theorems.Thm_BurkholderDFI_NonnegExp_tail_integral_bound
-- name    : BurkholderDFI.NonnegExp.tail_integral_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:12:05.616782+00:00
-- url     : https://prove2.me/theorems/8c63a0e5-0ff9-47ff-ac84-4648eb082b0d
-- title:
--   §18 — integrated tail bound with constant 3λ²
-- statement:
--   Let $f$ be a nonnegative martingale and $\mu=\inf\{n\ge1:|f_n|>\lambda\}$ for $\lambda>0$. For every $a>0$,
--
--   $$
--   \int_a^{\infty}P\bigl(S_{\mu-1}(f)^2>s\bigr)\,ds
--      \le 3\lambda^2P\bigl(S_{\mu-1}(f)^2>a\bigr).
--   $$
--
--   This is condition (18.4) for the stopped square function, with $\alpha=3\lambda^2$, and connects (18.5) to Lemma 18.1.
--
--   **Formalization Note** The square function and tail integral use $[0,\infty]$ values. The $3$ is the sum of the constants $1$ and $2$ on the two intervals displayed in the proof. Nonnegativity is almost everywhere at every positive time; Mathlib's index $0$ is auxiliary.
-- source:
--   Burkholder, Distribution Function Inequalities for Martingales, Ann. Probability 1 (1973), §18, proof of Theorem 18.1, p. 37; https://doi.org/10.1214/aop/1176997023

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

namespace BurkholderDFI.NonnegExp
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

/-- §18, proof of Theorem 18.1, p. 37: the tail condition (18.4) with α = 3λ². -/
theorem tail_integral_bound {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ P) (hnn : ∀ n, 1 ≤ n → 0 ≤ᵐ[P] f n)
    (l : ℝ) (hl : 0 < l) :
    ∀ a : ℝ, 0 < a →
      ∫⁻ s in Set.Ioi a, P {ω | ENNReal.ofReal s < BurkholderDFI.SquareFnLp.sqFnAt f (BurkholderDFI.SquareFnLp.exitTime f l ω - 1) ω ^ 2}
        ≤ ENNReal.ofReal (3 * l ^ 2) * P {ω | ENNReal.ofReal a < BurkholderDFI.SquareFnLp.sqFnAt f (BurkholderDFI.SquareFnLp.exitTime f l ω - 1) ω ^ 2} := by sorry

end BurkholderDFI.NonnegExp
