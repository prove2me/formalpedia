-- Prove2me | Theorems.Thm_BianchiIX_intervalRadiusInverse_positive_control
-- name    : BianchiIX.intervalRadiusInverse_positive_control
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-06T00:27:52.463448+00:00
-- url     : https://prove2.me/theorems/9b57b4e4-5588-4a09-bcd0-0b936d646ae6
-- title:
--   The increasing interval inverse agrees with ordinary local inverses
-- statement:
--   Let $a<b$, and let $f$ be $C^1$ at every point of $[a,b]$
--   with $f'>0$ there. Put $g=\operatorname{invFunOn}f\,[a,b]$.
--   Then $f$ is strictly increasing on $[a,b]$, its image is $[f(a),f(b)]$,
--   and $g$ is a two-sided inverse between these intervals. For every
--   $y\in(f(a),f(b))$, one has $g(y)\in(a,b)$, $g$ is $C^1$ at $y$,
--   and $g'(y)=1/f'(g(y))$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/PositiveIntervalInverse.lean#L10-L58

import Definitions.Def_BianchiIX_EraReturnData
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

theorem BianchiIX.intervalRadiusInverse_positive_control {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ∀ x ∈ Icc a b, ContDiffAt ℝ 1 f x)
    (hd : ∀ x ∈ Icc a b, 0 < deriv f x) :
    let g := intervalRadiusInverse f a b
    StrictMonoOn f (Icc a b) ∧ f '' Icc a b = Icc (f a) (f b) ∧
      LeftInvOn g f (Icc a b) ∧ MapsTo g (Icc (f a) (f b)) (Icc a b) ∧
      RightInvOn g f (Icc (f a) (f b)) ∧
      ∀ y ∈ Ioo (f a) (f b), g y ∈ Ioo a b ∧ ContDiffAt ℝ 1 g y ∧
        HasDerivAt g (deriv f (g y))⁻¹ y := by sorry
