-- Prove2me | Theorems.Thm_Erdos9796Mission_eq_of_dist_eq_three_of_pairwise_ne
-- name    : Erdos9796Mission.eq_of_dist_eq_three_of_pairwise_ne
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-12T22:50:58.614518+00:00
-- url     : https://prove2.me/theorems/af0d62de-fdae-4823-a2f2-8d2d63b03af9
-- title:
--   Three distinct reference points determine an equidistant center
-- statement:
--   Let P, Q, and R be pairwise-distinct points in the Euclidean plane. If A and B are each equidistant from P, Q, and R, then A = B.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/0c299d91bce69e27bc31a249cfbbf901db431505/lean/Erdos9796Proof/P97/N4d/SmallSReductions.lean#L372-L422

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Adam McKenna <adam@mysticflounder.ai>
-/

import Definitions.Def_Erdos9796Mission

open Erdos9796Mission

/-! Three pairwise-distinct reference points determine an equidistant center. -/

theorem Erdos9796Mission.eq_of_dist_eq_three_of_pairwise_ne
    (P Q R A B : Plane)
    (hPQ : P ≠ Q) (hPR : P ≠ R) (hQR : Q ≠ R)
    (hAP_AQ : dist A P = dist A Q) (hAP_AR : dist A P = dist A R)
    (hBP_BQ : dist B P = dist B Q) (hBP_BR : dist B P = dist B R) :
    A = B := by sorry
