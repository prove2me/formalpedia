-- Prove2me | Theorems.Thm_Erdos9796Mission_normalized_mutual_return_height_lt
-- name    : Erdos9796Mission.normalized_mutual_return_height_lt
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-12T22:08:17.058685+00:00
-- url     : https://prove2.me/theorems/09ac9ffb-253c-4cc9-bb39-07c6bd82c39a
-- title:
--   A guarded two-circle return has a sharp height bound
-- statement:
--   Let five points of a finite planar set in strictly convex position satisfy the listed noncoincidence relations. Suppose an injective affine chart sends two endpoints to (-1,0) and (1,0), points O and c to (0,-σh) and (0,σk), and the return point to (x,σy), where σ is 1 or -1, s is positive with s² = 3, 1 < h, and 0 < k ≤ 1. If the two listed equal-distance equations hold and an affine functional is positive on the left endpoint and c but negative on O and the return point, then k < 2 - s.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/04b4513a587040d0d9f5b24ab5500123fc60d48b/lean/Erdos9796Proof/P97/ATail/ExactFiveMutualReturnChord.lean#L185-L320

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Definitions.Def_Erdos9796Mission_NormalizedMutualReturn

open scoped EuclideanGeometry

open Erdos9796Mission

/-!
# The sharp normalized height bound

This theorem records the quantitative affine-geometric leaf proved by the
companion solution.
-/

theorem Erdos9796Mission.normalized_mutual_return_height_lt
    {A : Finset Plane} (hconv : ConvexIndep A) {q w O c b : Plane}
    (hqA : q ∈ A) (hwA : w ∈ A) (hOA : O ∈ A) (hcA : c ∈ A) (hbA : b ∈ A)
    (hbO : b ≠ O) (hbq : b ≠ q) (hbw : b ≠ w) (hcq : c ≠ q) (hOq : O ≠ q)
    (F : Plane →ᵃ[ℝ] Plane) (hF : Function.Injective F)
    {h k x y s σ : ℝ} (_hσ : σ = 1 ∨ σ = -1)
    (hsq : s ^ 2 = 3) (hs : 0 < s) (hh : 1 < h) (hk : 0 < k) (hk1 : k ≤ 1)
    (hFq : F q = planePoint (-1) 0) (hFw : F w = planePoint 1 0)
    (hFO : F O = planePoint 0 (-σ * h)) (hFc : F c = planePoint 0 (σ * k))
    (hFb : F b = planePoint x (σ * y))
    (heq1 : (x + 1) ^ 2 + y ^ 2 = 1 + k ^ 2)
    (heq2 : x ^ 2 + (y - k) ^ 2 = 1 + k ^ 2)
    (L : Plane →ᵃ[ℝ] ℝ)
    (hLq : 0 < L q) (hLc : 0 < L c) (hLO : L O < 0) (hLb : L b < 0) :
    k < 2 - s := by sorry
