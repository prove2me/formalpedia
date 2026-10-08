-- Prove2me | Theorems.Thm_BurkholderDFI_BMO_tail_integral_bound
-- name    : BurkholderDFI.BMO.tail_integral_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:16:03.707434+00:00
-- url     : https://prove2.me/theorems/ff68e9a6-3199-4f93-96e7-d46d28939f42
-- title:
--   §19 — tail integral bound for the square function under (19.1)
-- statement:
--   Let $f$ be a real martingale on a probability space, adapted to $(\mathcal A_n)$, with difference sequence $d$. Assume condition (19.1): for every $n\ge1$, the conditional expectation of $\sum_{k=n}^{\infty}d_k^2$ given $\mathcal A_n$ is at most one almost surely. For $S(f)^2=\sum_{k=1}^{\infty}d_k^2$ and every $a>0$,
--
--   $$\int_a^\infty P\big(S(f)^2>x\big)\,dx\le P\big(S(f)^2>a\big).$$
--
--   This is the tail estimate displayed in the proof of Theorem 19.1. It supplies the hypothesis of Lemma 18.1 with $g=S(f)^2$ and $\alpha=1$.
--
--   **Formalization Note** The paper proves this inside a theorem about martingales, and the formal statement retains the martingale hypothesis. Both the square function and the tail integral are extended nonnegative values, so an infinite square function cannot be hidden by a default real value. Mathlib's martingale includes a value at index zero; any martingale of the paper extends to one by assigning its conditional expectation at zero. The difference sequence still uses the paper's $f_0=0$.
-- source:
--   Burkholder, Distribution Function Inequalities for Martingales, Ann. Probability 1 (1973), §19, proof of Theorem 19.1, p. 37, https://doi.org/10.1214/aop/1176997023

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale
import Definitions.Def_BurkholderDFI_BMO_Condition

namespace BurkholderDFI.BMO

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- §19, proof of Theorem 19.1, p. 37: the tail integral of `S(f)²` under (19.1). -/
theorem tail_integral_bound {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ P) (h191 : BMOCondition ℱ P f) :
    ∀ a : ℝ, 0 < a →
      ∫⁻ x in Set.Ioi a, P {ω | ENNReal.ofReal x < BurkholderDFI.SquareFnLp.sqFn f ω ^ 2}
        ≤ P {ω | ENNReal.ofReal a < BurkholderDFI.SquareFnLp.sqFn f ω ^ 2} := by sorry

end BurkholderDFI.BMO
