-- Prove2me | Theorems.Thm_BurkholderDFI_SquareFnLp_duality_bound
-- name    : BurkholderDFI.SquareFnLp.duality_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:54:47.514838+00:00
-- url     : https://prove2.me/theorems/f9c362c3-2619-4461-bd38-9270a8a7955b
-- title:
--   §3, proof of Theorem 3.2 — ‖f_n‖_p ≤ 18q^{1/2}p‖S_n(f)‖_p for every martingale
-- statement:
--   Let $f = (f_1, f_2, \dots)$ be a martingale relative to $\mathcal A_1 \subseteq \mathcal A_2 \subseteq \cdots$ and let $n$ be a positive integer. For every $1 < p < \infty$, with $p^{-1} + q^{-1} = 1$,
--   $$\|f_n\|_p \le 18\, q^{1/2} p\, \|S_n(f)\|_p .$$
--
--   This is the right side of Theorem 3.2 at a fixed time $n$, with the explicit constant $C_p = 18 q^{1/2} p$; the paper derives it from (3.7) applied in the dual exponent $q$.
--
--   **Formalization Note** Norms are computed in $[0, \infty]$; when $\|S_n(f)\|_p = \infty$ the bound is trivial. The Mathlib convention at index $0$ is as in (1.1).
-- source:
--   Burkholder, Distribution Function Inequalities for Martingales, Ann. Probability 1 (1973), §3, proof of Theorem 3.2, p. 23 (display after (3.7))

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

namespace BurkholderDFI.SquareFnLp

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

theorem duality_bound {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ P) (n : ℕ) (hn : 1 ≤ n) (p q : ℝ) (hp : 1 < p) (hpq : p⁻¹ + q⁻¹ = 1) :
    lpNormE P p (fun ω => ENNReal.ofReal |f n ω|)
      ≤ ENNReal.ofReal (18 * Real.sqrt q * p) * lpNormE P p (sqFnN f n) := by sorry

end BurkholderDFI.SquareFnLp
