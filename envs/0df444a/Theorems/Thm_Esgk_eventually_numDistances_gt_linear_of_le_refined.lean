-- Prove2me | Theorems.Thm_Esgk_eventually_numDistances_gt_linear_of_le_refined
-- name    : Esgk.eventually_numDistances_gt_linear_of_le_refined
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-10-20T05:21:55.138546+00:00
-- url     : https://prove2.me/theorems/5c1fdd05-68f9-4038-ba59-a0c65ff8def0
-- title:
--   Eventually more than $A\,n$ distinct distances in general position for every $A\le 1/3+1/130$
-- statement:
--   Let $A$ be a real number with $A\le 1/3+1/130$. Then there is a threshold $N$ such that the following holds for every $n\ge N$. Let $p=(p_1,\dots,p_n)$ be an injective configuration of $n$ points in the plane whose image $P=\{p_1,\dots,p_n\}$ has no three collinear points and no four points on a common circle, and let $D(P)$ be the number of distinct distances between distinct points of $P$. Then
--
--   $$
--   D(P)>A\,n .
--   $$
--
--   The threshold may depend on $A$, and the conclusion holds for every qualifying configuration of size $n$. This is the eventual, fixed-coefficient form of the bound $D(P)>(1/3+1/130)n$ for $n\ge 10000$. Erdős Problem 98 asks for this conclusion for every real $A>0$; the statement here covers the coefficients $A\le 1/3+1/130$ only.
--
--   **Formalization Note** The threshold is expressed with `Filter.atTop` on the natural numbers, and $D(P)$ is `NumDistances p`.
-- source:
--   Context: Erdős Problem 98, https://www.erdosproblems.com/98. Lean formalization by Adam McKenna (2026), declaration Esgk.eventually_numDistances_gt_linear_of_le_refined.

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import Definitions.Def_Esgk_Energy
import Definitions.Def_Esgk_Foundation
import Definitions.Def_Esgk_PlanarGeneralPosition

open EuclideanGeometry Esgk

namespace Esgk

theorem eventually_numDistances_gt_linear_of_le_refined
    (A : ℝ) (hA : A ≤ 1 / 3 + 1 / 130) :
    ∀ᶠ n in Filter.atTop,
      ∀ p : Config n,
        Function.Injective p →
        InGeneralPosition (Config.toFinset p) →
        A * (n : ℝ) < (NumDistances p : ℝ) := by sorry

end Esgk
