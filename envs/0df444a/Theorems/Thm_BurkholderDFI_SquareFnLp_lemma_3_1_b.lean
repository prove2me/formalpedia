-- Prove2me | Theorems.Thm_BurkholderDFI_SquareFnLp_lemma_3_1_b
-- name    : BurkholderDFI.SquareFnLp.lemma_3_1_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:55:13.99357+00:00
-- url     : https://prove2.me/theorems/c6da0f36-94b6-44cb-b743-04345d49413d
-- title:
--   Lemma 3.1, (3.5) — ‖S_n(f)‖_p ≤ 9p^{1/2}q‖f_n‖_p for nonnegative submartingales
-- statement:
--   Let $f = (f_1, f_2, \dots)$ be a nonnegative submartingale relative to $\mathcal A_1 \subseteq \mathcal A_2 \subseteq \cdots$ and let $n$ be a positive integer. For every $1 < p < \infty$, with $p^{-1} + q^{-1} = 1$,
--   $$\|S_n(f)\|_p \le 9\, p^{1/2} q\, \|f_n\|_p , \tag{3.5}$$
--   where $S_n(f) = \bigl(\sum_{k=1}^n d_k^2\bigr)^{1/2}$ and $\|\cdot\|_p = (E|\cdot|^p)^{1/p}$.
--
--   This is the explicit-constant square function inequality for nonnegative submartingales; applied to the positive and negative parts of a martingale it gives the left side of Theorem 3.2.
--
--   **Formalization Note** Norms are computed in $[0, \infty]$, so $\|f_n\|_p = \infty$ is allowed (the bound is then trivial). "Nonnegative" means almost everywhere, for $k \ge 1$. The Mathlib convention at index $0$ is as in (1.1). This is the second half of the paper's Lemma 3.1.
-- source:
--   Burkholder, Distribution Function Inequalities for Martingales, Ann. Probability 1 (1973), Lemma 3.1, p. 22, display (3.5)

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

namespace BurkholderDFI.SquareFnLp

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

theorem lemma_3_1_b {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hsub : Submartingale f ℱ P) (hnn : ∀ n, 1 ≤ n → 0 ≤ᵐ[P] f n)
    (n : ℕ) (hn : 1 ≤ n) (p q : ℝ) (hp : 1 < p) (hpq : p⁻¹ + q⁻¹ = 1) :
    lpNormE P p (sqFnN f n)
      ≤ ENNReal.ofReal (9 * Real.sqrt p * q) * lpNormE P p (fun ω => ENNReal.ofReal |f n ω|) := by sorry

end BurkholderDFI.SquareFnLp
