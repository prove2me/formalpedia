-- Prove2me | Theorems.Thm_BurkholderDFI_ConvexPhi_eq_1_5
-- name    : BurkholderDFI.ConvexPhi.eq_1_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:11:45.267242+00:00
-- url     : https://prove2.me/theorems/2def39d8-cad4-44cc-82da-580ea2bebb4d
-- title:
--   (1.5) — Doob's weak-type maximal estimate (cited)
-- statement:
--   Let $f$ be a martingale or a nonnegative submartingale and let $1\le p<\infty$. For every $\lambda>0$,
--   $$
--   \lambda^p P(f^*>\lambda)\le\|f\|_p^p,
--   \qquad \|f\|_p=\sup_{n\ge1}(E|f_n|^p)^{1/p}.
--   $$
--   Burkholder cites this consequence of Doob's inequality and uses it in the proof of (12.3).
--
--   **Formalization Note** Nonnegativity of a submartingale is almost everywhere at every positive index. Extended nonnegative norms retain the infinite case; Mathlib's process includes an index-zero extension that these functionals ignore.
-- source:
--   Burkholder, Distribution Function Inequalities for Martingales, Ann. Probability 1 (1973), (1.5), p. 20

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

namespace BurkholderDFI.ConvexPhi
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- (1.5), p. 20: Doob's cited weak-type estimate. -/
theorem eq_1_5 {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ P ∨ (Submartingale f ℱ P ∧ ∀ n, 1 ≤ n → 0 ≤ᵐ[P] f n))
    (p : ℝ) (hp : 1 ≤ p) (l : ℝ) (hl : 0 < l) :
    ENNReal.ofReal (l ^ p) * P {ω | ENNReal.ofReal l < BurkholderDFI.SquareFnLp.maxFn f ω} ≤ BurkholderDFI.SquareFnLp.pNorm P p f ^ p := by sorry
end BurkholderDFI.ConvexPhi
