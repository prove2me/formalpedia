-- Prove2me | Theorems.Thm_FBMStrongSim_RecordBreak_Supplement_lemma_5_8
-- name    : FBMStrongSim.RecordBreak.Supplement.lemma_5_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T22:33:56.864264+00:00
-- url     : https://prove2.me/theorems/b2ef9ab9-0f36-4994-93bd-21707bd8340f
-- title:
--   Lemma 5.8 — (corrected: dimension factor and time order) Euler grid estimates
-- statement:
--   Use the bounded $C^2$ field, $\alpha$-Hölder driver, dimensions and positive envelopes described in Lemma 5.7. For every initial value and every level $n\ge0$, the Euler scheme obeys
--   $$|y_n(t_j^n)-y_n(t_r^n)|\le G_1|t_j^n-t_r^n|^\alpha\quad(0\le j,r\le2^n),$$
--   $$|y_n(t_j^n)-y_n(t_r^n)-f(y_n(t_r^n))(x(t_j^n)-x(t_r^n))|\le G_2|t_j^n-t_r^n|^{2\alpha}\quad(0\le r\le j\le2^n).$$
--   Here $G_1,G_2$ use the corrected $L$ in YoungConstants. The estimate supplies grid regularity and forward local error for the Euler rate theorem, including coarse grids.
--
--   Differences from the source:
--   - reading: absolute values of vectors, matrices and derivatives → maximum vector norm and maximum absolute derivative entries; reason: the explicit norm convention planned in the brief, making all dimension factors checkable
--   - correction: constants evaluated at the exact derivative norms, including zero norms → F0,F1 are positive uniform entrywise envelopes and F2 is a nonnegative uniform entrywise envelope; reason: the printed ω divides by L=0 for constant fields; for α<1 the printed G1* is also zero when ∇f=0 although a nonzero constant field has a nonconstant solution; see DISPROOF.md; every bounded C² field admits these envelopes
--   - correction: L=4(hC)²F1F0/(1−2^(1−2α)) on p. 30 → Lcorr=4d(hC)²F1F0/(1−2^(1−2α)), used in correctedG1 and correctedG2 for Lemma 5.8 only; reason: Appendix C.2 p. 45 needs the bound |f(a)−f(b)|≤dF1|a−b|; DISPROOF.md exhibits d=1024,h=1,α=1,n=10 where the printed Lemma 5.8 remainder fails by a factor 13.29; no dimension, grid or vector field is excluded
--   - correction: the printed second estimate for all j,r and the symbol y^(n) → the first estimate for all pairs, the forward remainder for r≤j, and y_n in both; reason: Appendix C.2 pp. 44–45 proves the remainder with the coefficient evaluated at the earlier point; reversing one Euler step adds a nonzero coefficient difference whereas its forward remainder is zero
-- source:
--   Chen, Dong & Ni, ε-Strong simulation of fractional Brownian motion and related stochastic differential equations, arXiv:1902.07824v1, p. 31, Lemma 5.8

import Mathlib
import Definitions.Def_FBMStrongSim_RecordBreak_Supplement_HolderModel
import Definitions.Def_FBMStrongSim_RecordBreak_Supplement_YoungModel
import Definitions.Def_FBMStrongSim_RecordBreak_Supplement_EulerModel
import Definitions.Def_FBMStrongSim_RecordBreak_Supplement_GridHolderModel
import Definitions.Def_FBMStrongSim_RecordBreak_Supplement_YoungConstants

namespace FBMStrongSim.RecordBreak.Supplement

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Lemma 5.8 (p.31), corrected entrywise constant L; the remainder is forward in time. -/
theorem lemma_5_8 {d h : ℕ} (hd : 0 < d) (hh : 0 < h) {alpha C F0 F1 F2 : ℝ}
    (ha : 1 / 2 < alpha) (ha1 : alpha ≤ 1) (hC : 0 < C)
    {f : Field d h} (hf : CoefficientBounds f F0 F1 F2)
    {x : ℝ → Vec h} (hx : HolderBound alpha C x)
    (y0 : Vec d) (n : ℕ) :
    (∀ j r : ℕ, j ≤ 2 ^ n → r ≤ 2 ^ n →
      ‖eulerValue f x y0 n j - eulerValue f x y0 n r‖ ≤
        correctedG1 d h alpha C F0 F1 * |dyadic n j - dyadic n r| ^ alpha) ∧
    (∀ r j : ℕ, r ≤ j → j ≤ 2 ^ n →
      ‖eulerValue f x y0 n j - eulerValue f x y0 n r -
          f (eulerValue f x y0 n r) (x (dyadic n j) - x (dyadic n r))‖ ≤
        correctedG2 d h alpha C F0 F1 * (dyadic n j - dyadic n r) ^ (2 * alpha)) := by sorry

end FBMStrongSim.RecordBreak.Supplement
