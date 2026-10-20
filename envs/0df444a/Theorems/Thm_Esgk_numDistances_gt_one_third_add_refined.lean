-- Prove2me | Theorems.Thm_Esgk_numDistances_gt_one_third_add_refined
-- name    : Esgk.numDistances_gt_one_third_add_refined
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-10-20T05:18:42.978518+00:00
-- url     : https://prove2.me/theorems/fbd96e6f-935a-4deb-9513-9fe4a8f9157a
-- title:
--   More than $(1/3+1/130)\,n$ distinct distances in general position for $n\ge 10000$
-- statement:
--   Let $n\ge 10000$ and let $p=(p_1,\dots,p_n)$ be an injective configuration of $n$ points in the plane, with image $P=\{p_1,\dots,p_n\}$. Assume that $P$ is in general position: no three points of $P$ are collinear and no four points of $P$ lie on a common circle. Let $D(P)$ be the number of distinct distances $|x-y|$ with $x,y\in P$ and $x\ne y$. Then
--
--   $$
--   D(P)>\Bigl(\frac13+\frac1{130}\Bigr)n .
--   $$
--
--   A circle about a point of $P$ contains at most three other points of $P$, which gives $3D(P)\ge n-1$. The theorem raises the coefficient $1/3$ by the explicit amount $1/130$ for every $n\ge 10000$. Erdős Problem 98 asks whether the minimum of $D(P)$ over general-position sets of $n$ points grows faster than every linear function of $n$; this theorem gives the linear lower bounds with coefficient at most $1/3+1/130$ only.
--
--   **Formalization Note** $D(P)$ is `NumDistances p`, the number of distances between distinct points of `Config.toFinset p`. General position is `InGeneralPosition`, in which "on a common circle" is Mathlib's `Cospherical` in the Euclidean plane.
-- source:
--   Context: Erdős Problem 98, https://www.erdosproblems.com/98. Lean formalization by Adam McKenna (2026), declaration Esgk.numDistances_gt_one_third_add_refined.

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

theorem numDistances_gt_one_third_add_refined {n : ℕ} {p : Config n}
    (hp : Function.Injective p) (hgp : InGeneralPosition (Config.toFinset p))
    (hn : 10000 ≤ n) :
    (1 / 3 + 1 / 130) * (n : ℝ) < (NumDistances p : ℝ) := by sorry

end Esgk
