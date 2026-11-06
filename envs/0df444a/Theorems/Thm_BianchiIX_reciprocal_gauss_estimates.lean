-- Prove2me | Theorems.Thm_BianchiIX_reciprocal_gauss_estimates
-- name    : BianchiIX.reciprocal_gauss_estimates
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T07:06:01.422134+00:00
-- url     : https://prove2.me/theorems/3e973ea4-bd40-4287-be40-f7fd94046810
-- title:
--   Reciprocal branches preserve digit-square value accuracy and logarithmic distortion
-- statement:
--   Let $k:\mathbb R\to\mathbb R$, $n\geq1$, $y\geq0$,
--   $k(y)\geq n$, and suppose $k'(y)=d>0$,
--   $|k(y)-(n+y)|\leq E\leq1/4$, and $|\log d|\leq D$.
--   For $h(z)=1/k(z)$ and $g_n(z)=1/(n+z)$, one has
--   $$h'(y)=-d/k(y)^2<0,\qquad |h(y)-g_n(y)|\leq E/n^2,$$
--   $$\left|\log\frac{|h'(y)|}{|g_n'(y)|}\right|\leq D+4E.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/ReciprocalGaussEstimates.lean#L8-L52

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Induction

noncomputable section
open BianchiIX

theorem BianchiIX.reciprocal_gauss_estimates {k : ℝ → ℝ} {n y d E D : ℝ}
    (hn : 1 ≤ n) (hy : 0 ≤ y) (hk : n ≤ k y)
    (Hk : HasDerivAt k d y) (hd : 0 < d)
    (hvalue : |k y - (n + y)| ≤ E) (hsmall : E ≤ 1 / 4)
    (hlog : |Real.log d| ≤ D) :
    let h := fun z => 1 / k z
    HasDerivAt h (-d / (k y) ^ 2) y ∧ deriv h y < 0 ∧
      |h y - gaussInv n y| ≤ E / n ^ 2 ∧
      |Real.log (|deriv h y| / |deriv (gaussInv n) y|)| ≤ D + 4 * E := by sorry
