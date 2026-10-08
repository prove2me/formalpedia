-- Prove2me | Theorems.Thm_BurkholderDFI_SquareFnLp_eq_3_7
-- name    : BurkholderDFI.SquareFnLp.eq_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:54:38.07388+00:00
-- url     : https://prove2.me/theorems/1d1ba921-c7ea-4254-9ff6-3a41969ab298
-- title:
--   (3.7) — ‖S_n(f)‖_p ≤ 18p^{1/2}q‖f_n‖_p for every martingale
-- statement:
--   Let $f = (f_1, f_2, \dots)$ be a martingale relative to $\mathcal A_1 \subseteq \mathcal A_2 \subseteq \cdots$ and let $n$ be a positive integer. For every $1 < p < \infty$, with $p^{-1} + q^{-1} = 1$,
--   $$\|S_n(f)\|_p \le 18\, p^{1/2} q\, \|f_n\|_p . \tag{3.7}$$
--
--   This is the left side of Theorem 3.2 at a fixed time $n$, with the explicit constant $c_p = (18 p^{1/2} q)^{-1}$; it is also the input of the duality argument for the right side.
--
--   **Formalization Note** Norms are computed in $[0, \infty]$. The Mathlib convention at index $0$ is as in (1.1). The paper writes this inequality as the last line of the display (3.7) in the proof of Theorem 3.2.
-- source:
--   Burkholder, Distribution Function Inequalities for Martingales, Ann. Probability 1 (1973), proof of Theorem 3.2, p. 23, display (3.7)

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

namespace BurkholderDFI.SquareFnLp

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

theorem eq_3_7 {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ P) (n : ℕ) (hn : 1 ≤ n) (p q : ℝ) (hp : 1 < p) (hpq : p⁻¹ + q⁻¹ = 1) :
    lpNormE P p (sqFnN f n)
      ≤ ENNReal.ofReal (18 * Real.sqrt p * q) * lpNormE P p (fun ω => ENNReal.ofReal |f n ω|) := by sorry

end BurkholderDFI.SquareFnLp
