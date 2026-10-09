-- Prove2me | Theorems.Thm_AffineVolterra_RiccatiSqrt_eq_3_9_3_10
-- name    : AffineVolterra.RiccatiSqrt.eq_3_9_3_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:48:32.936105+00:00
-- url     : https://prove2.me/theorems/eda9a98b-034b-4c95-81f4-7ade04ed98a0
-- title:
--   Proof of Theorem 3.6, (3.9)–(3.10), p. 16 — shifted resolvent convolution
-- statement:
--   Let $K$ satisfy conditions (2.5) and (3.4), with nonnegative resolvent of the first kind $L$, and fix $h>0$. The convolution of the shifted kernel with $L$ is nondecreasing in time and lies between zero and one:
--   $$
--   t\longmapsto (\Delta_h K*L)(t)\text{ is nondecreasing},\qquad
--   0\le (\Delta_h K*L)(t)\le 1\quad(t\ge0).
--   $$
--   Its defining integral is required to exist at every nonnegative time. This bound is the kernel comparison used in the invariance argument.
--
--   **Formalization Note** At $t=0$, the right-continuous extension in the paper is represented by the integral over $[0,0]$; the displayed bound is the clause used downstream. Condition (3.4) names its resolvent measure for this statement.
-- source:
--   Abi Jaber, Larsson and Pulido, Affine Volterra processes, arXiv:1708.08796v3, proof of Theorem 3.6, p. 16, (3.9)–(3.10)

import Mathlib
import Definitions.Def_AffineVolterra_RiccatiSqrt_Setting

namespace AffineVolterra.RiccatiSqrt

open MeasureTheory

/-- Proof of Theorem 3.6, (3.9)–(3.10), p. 16. -/
theorem eq_3_9_3_10 (k : ℝ → ℝ) (L : Measure ℝ) (h : ℝ)
    (h25 : ∃ γ : ℝ, Cond25 k γ) (hk : Cond34With k L) (hh : 0 < h) :
    MonotoneOn (fun t : ℝ => ∫ s in Set.Icc 0 t, k (t + h - s) ∂L)
      (Set.Ici 0) ∧
    ∀ t : ℝ, 0 ≤ t →
      IntegrableOn (fun s => k (t + h - s)) (Set.Icc 0 t) L ∧
      0 ≤ (∫ s in Set.Icc 0 t, k (t + h - s) ∂L) ∧
      (∫ s in Set.Icc 0 t, k (t + h - s) ∂L) ≤ 1 := by sorry

end AffineVolterra.RiccatiSqrt
