-- Prove2me | Theorems.Thm_BurkholderDFI_SquareFnLp_theorem_3_2
-- name    : BurkholderDFI.SquareFnLp.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:54:40.882975+00:00
-- url     : https://prove2.me/theorems/dd176e00-94a3-410c-86f0-d010484af687
-- title:
--   Theorem 3.2 — for 1 < p < ∞, c_p‖S(f)‖_p ≤ ‖f‖_p ≤ C_p‖S(f)‖_p for every martingale
-- statement:
--   Let $1 < p < \infty$. There are positive real numbers $c_p$ and $C_p$, depending only on $p$, such that for every probability space $(\Omega, \mathcal A, P)$, every filtration $\mathcal A_1 \subseteq \mathcal A_2 \subseteq \cdots$ and every martingale $f = (f_1, f_2, \dots)$ relative to it,
--   $$c_p \|S(f)\|_p \le \|f\|_p \le C_p \|S(f)\|_p , \tag{3.3}$$
--   where $S(f) = \bigl(\sum_{k=1}^\infty d_k^2\bigr)^{1/2}$ is the square function of $f$, $d_k = f_k - f_{k-1}$ ($f_0 = 0$), $\|S(f)\|_p = (E\,S(f)^p)^{1/p}$, and $\|f\|_p = \sup_{n \ge 1} \|f_n\|_p$.
--
--   In particular a martingale is $L^p$-bounded exactly when its square function is in $L^p$. This is Burkholder's square function inequality (1966), the basic $L^p$ comparison of martingale theory for $1 < p < \infty$.
--
--   **Formalization Note** The constants are chosen before the probability space, the filtration and the martingale, so they depend only on $p$. Both $\|f\|_p$ and $\|S(f)\|_p$ are computed in $[0, \infty]$ and neither is assumed finite, so the statement includes "$\|f\|_p = \infty$ if and only if $\|S(f)\|_p = \infty$". The paper's martingale relative to $\mathcal A_1, \mathcal A_2, \dots$ is a Mathlib martingale indexed by $\mathbb N$, whose value at index $0$ the statement never reads; this is no restriction (set $f_0 := E(f_1 \mid \mathcal A_0)$). The probability space lives in `Type` (universe 0). The remark after the theorem about the growth of the optimal constants, $c_p^{-1} = O(p^{1/2}q)$ and $C_p = O(q^{1/2}p)$, is not part of the statement; the explicit constants of the proof are the milestones (3.7) and the duality bound.
-- source:
--   Burkholder, Distribution Function Inequalities for Martingales, Ann. Probability 1 (1973), Theorem 3.2, p. 22, display (3.3)

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

namespace BurkholderDFI.SquareFnLp

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

theorem theorem_3_2 (p : ℝ) (hp : 1 < p) :
    ∃ c C : ℝ≥0, 0 < c ∧ 0 < C ∧
      ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ℱ : Filtration ℕ mΩ) (f : ℕ → Ω → ℝ), Martingale f ℱ P →
        (c : ℝ≥0∞) * lpNormE P p (sqFn f) ≤ pNorm P p f ∧
          pNorm P p f ≤ (C : ℝ≥0∞) * lpNormE P p (sqFn f) := by sorry

end BurkholderDFI.SquareFnLp
