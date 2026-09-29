-- Prove2me | Theorems.Thm_CohCarrier_index_range_iotaDeg_of_prime_comap
-- name    : CohCarrier.index_range_iotaDeg_of_prime_comap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/7579e744-63bf-548e-ba51-5c049f0e8394
-- title:
--   Degeneracy images at level Nq: indices q+1, q+1, 1, 1
-- statement:
--   Let $N$ and $q$ be nonzero natural numbers with $q$ prime and $q \nmid N$, and let $H \le (\mathbb{Z}/N)^\times$. Write $H' = H.\mathrm{comap}\,(\mathbb{Z}/Nq)^\times \to (\mathbb{Z}/N)^\times$ for the full preimage of $H$ under the reduction map on units attached to $N \mid Nq$, and let $\Gamma_H(M)$ denote the subgroup of $SL_2(\mathbb{Z})$ obtained as the image in $SL_2(\mathbb{Z})$ of the matrices of $\Gamma_0(M)$ whose associated diagonal unit lies in the prescribed subgroup. Assume the two hypotheses `LevelLE N (N*q) H H' 1` and `LevelLE N (N*q) H H' q`, each asserting $N \mid Nq$, that the respective $d \in \{1,q\}$ divides $(Nq)/N$, and that $H'$ reduces into $H$. For $d \in \{1,q\}$ the homomorphism `iotaDeg` sends $\gamma = \begin{pmatrix} a & b \\ c & e\end{pmatrix} \in \Gamma_{H'}(Nq)$ to $\begin{pmatrix} a & bd \\ c/d & e\end{pmatrix} \in \Gamma_H(N)$. The conclusion is fourfold: the image of `iotaDeg` for $d = 1$ has index $q+1$ in $\Gamma_H(N)$; the image for $d = q$ has index $q+1$ in $\Gamma_H(N)$; the intersection of the image for $d = q$ with $\Gamma_H(N) \cap \Gamma^0(q)$ has index $1$ in the latter, i.e. $\Gamma_H(N) \cap \Gamma^0(q)$ is contained in that image; and likewise $\Gamma_H(N) \cap \Gamma_0(qN)$ is contained in the image for $d = 1$. Here $\Gamma^0(q)$ is the subgroup of $SL_2(\mathbb{Z})$ with upper right entry divisible by $q$, and both intersections are formed inside $\Gamma_H(N)$.
--
--   These are the indices of the two degeneracy images in the level-raising comparison between $\Gamma_{H'}(Nq)$ and $\Gamma_H(N)$ for $H'$ the full preimage of $H$: each image has index $q+1$, and the images coincide with $\Gamma_H(N) \cap \Gamma_0(qN)$ and $\Gamma_H(N) \cap \Gamma^0(q)$ respectively. The four numbers $q+1, q+1, 1, 1$ feed the composition bookkeeping of the degeneracy tower used in the construction of the local Hecke module at the auxiliary prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_index_range_iotaDeg_of_prime_comap.lean

import Mathlib
import Definitions.Def_CohCarrier_Lower

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CohCarrier CongruenceSubgroup
open scoped MatrixGroups

theorem CohCarrier.index_range_iotaDeg_of_prime_comap (N q : ℕ) [NeZero N] [NeZero q]
    (hq : q.Prime) (hqN : ¬ q ∣ N) (H : Subgroup (ZMod N)ˣ)
    (h₁ : LevelLE N (N * q) H (H.comap (ZMod.unitsMap (dvd_mul_right N q))) 1)
    (hq' : LevelLE N (N * q) H (H.comap (ZMod.unitsMap (dvd_mul_right N q))) q) :
    (iotaDeg N (N * q) H (H.comap (ZMod.unitsMap (dvd_mul_right N q))) 1 h₁).range.index = q + 1 ∧
    (iotaDeg N (N * q) H (H.comap (ZMod.unitsMap (dvd_mul_right N q))) q hq').range.index = q + 1 ∧
    ((iotaDeg N (N * q) H (H.comap (ZMod.unitsMap (dvd_mul_right N q))) q hq').range.subgroupOf (GammaHUpper N H q)).index = 1 ∧
    ((iotaDeg N (N * q) H (H.comap (ZMod.unitsMap (dvd_mul_right N q))) 1 h₁).range.subgroupOf (GammaHLower N H q)).index = 1 := by sorry
