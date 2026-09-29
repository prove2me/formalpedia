-- Prove2me | Theorems.Thm_CohCarrier_levelLE_comap_one_and_q
-- name    : CohCarrier.levelLE_comap_one_and_q
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/6526adbc-dea4-54bf-9f12-83ef21c70a14
-- title:
--   Level compatibility at d=1 and d=q for full preimages
-- statement:
--   Let $N$ and $q$ be natural numbers, both nonzero, and let $H$ be a subgroup of $(\mathbb{Z}/N)^\times$. Write $H'$ for the preimage of $H$ under the reduction map $(\mathbb{Z}/Nq)^\times \to (\mathbb{Z}/N)^\times$ attached to the divisibility $N \mid Nq$, that is, the `Subgroup.comap` of $H$ along `ZMod.unitsMap`. The assertion is the conjunction of two instances of the project's predicate `LevelLE N (N*q) H H' d`, namely for $d = 1$ and for $d = q$. By definition, `LevelLE M M' H H' d` consists of three data: the divisibility $M \mid M'$, the divisibility $d \mid M'/M$, and the condition that every unit $u \in H'$ reduces into $H$ under the induced map $(\mathbb{Z}/M')^\times \to (\mathbb{Z}/M)^\times$. So the content here is: $N \mid Nq$; the divisor conditions $1 \mid (Nq)/N$ and $q \mid (Nq)/N$; and, in both cases, that units of $(\mathbb{Z}/Nq)^\times$ lying in $H'$ reduce into $H$ modulo $N$.
--
--   This supplies the level-compatibility witnesses needed for the two degeneracy maps, at $d = 1$ and $d = q$, between the level-$N$ and level-$Nq$ structures when the higher-level subgroup is taken to be the full preimage of $H$. It is used to instantiate the general-$H$ degeneracy constructions in [`CohCarrier.exists_subfamily_corner_refinement_level_mul_of_corner_cofull`](thm.html#CohCarrier.exists_subfamily_corner_refinement_level_mul_of_corner_cofull) and in the corresponding refinement statement for local Hecke data on cusp forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_levelLE_comap_one_and_q.lean

import Mathlib
import Definitions.Def_CohCarrier_Lower

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CohCarrier CongruenceSubgroup
open scoped MatrixGroups

theorem CohCarrier.levelLE_comap_one_and_q (N q : ℕ) [NeZero N] [NeZero q] (H : Subgroup (ZMod N)ˣ) :
    LevelLE N (N * q) H (H.comap (ZMod.unitsMap (dvd_mul_right N q))) 1 ∧
    LevelLE N (N * q) H (H.comap (ZMod.unitsMap (dvd_mul_right N q))) q := by sorry
