-- Prove2me | Theorems.Thm_CohCarrier_jDeg_iDeg_nine_identities_of_prime
-- name    : CohCarrier.jDeg_iDeg_nine_identities_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/0c8358c8-a9aa-51c9-95be-d5d8861f5ab6
-- title:
--   The nine degeneracy compositions at level Nq²
-- statement:
--   Let $N,q$ be nonzero natural numbers with $q$ prime and $q\nmid N$, and let $A$ be an additive abelian group. Suppose given three instances `LevelLE N (N*q^2) ⊤ ⊤ d`, for $d=1,q,q^2$, each asserting that $N\mid Nq^2$, that $d\mid (Nq^2)/N$, and that reduction carries the full unit subgroup at level $Nq^2$ into the full unit subgroup at level $N$. Working in $H1\,N\,\top\,A$, the group of homomorphisms from $\Gamma_\top(N)$ to $A$, write $i_d=$ `iDeg'` for restriction along the conjugation map `iotaDeg` by the lower matrix of parameter $d$, and $j_d=$ `jDeg` for the transfer to $\Gamma_\top(N)$ of a character of the (finite-index) range of that map, transported by its inverse isomorphism; write $T_q=$ `heckeT N ⊤ q A` for the transfer along `conjL` from `GammaHUpper N ⊤ q`. The conclusion is the conjunction of nine identities, valid for every $\varphi$: $j_d(i_d\varphi)=q(q+1)\cdot\varphi$ for $d=1,q,q^2$; $j_d(i_{d'}\varphi)=q\cdot T_q\varphi$ for the four pairs $(d,d')$ with $\{d,d'\}=\{1,q\}$ or $\{q,q^2\}$; and $j_d(i_{d'}\varphi)=T_q(T_q\varphi)-(q+1)\cdot\varphi$ for $\{d,d'\}=\{1,q^2\}$, all scalars acting as integers.
--
--   These are the nine entries of the $3\times 3$ matrix of compositions of the degeneracy maps between levels $N$ and $Nq^2$ on additive characters, as used in level raising at a prime $q$ not dividing $N$: diagonal entries given by the index of the image subgroup, the neighbouring entries by $q T_q$, and the corner entries by $T_q^2-(q+1)$. The result is invoked in the construction of the level-raising combination `levelRaisingComb_mem_parabolicHoms_and_adjoint_and_comp_of_prime`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_jDeg_iDeg_nine_identities_of_prime.lean

import Definitions.Def_CohCarrier_Level

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CohCarrier in

theorem CohCarrier.jDeg_iDeg_nine_identities_of_prime (N q : ℕ) [NeZero N] [NeZero q]
    (A : Type) [AddCommGroup A] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (h1 : LevelLE N (N * q ^ 2) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) 1)
    (hq' : LevelLE N (N * q ^ 2) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) q)
    (hq2 : LevelLE N (N * q ^ 2) (⊤ : Subgroup (ZMod N)ˣ)
      (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) (q ^ 2)) :
    (∀ φ, (jDeg N (N*q^2) ⊤ ⊤ 1 A h1).comp (iDeg' N (N*q^2) ⊤ ⊤ 1 A h1) φ
        = (q * (q + 1) : ℤ) • φ) ∧
    (∀ φ, (jDeg N (N*q^2) ⊤ ⊤ q A hq').comp (iDeg' N (N*q^2) ⊤ ⊤ q A hq') φ
        = (q * (q + 1) : ℤ) • φ) ∧
    (∀ φ, (jDeg N (N*q^2) ⊤ ⊤ (q^2) A hq2).comp (iDeg' N (N*q^2) ⊤ ⊤ (q^2) A hq2) φ
        = (q * (q + 1) : ℤ) • φ) ∧
    (∀ φ, (jDeg N (N*q^2) ⊤ ⊤ 1 A h1).comp (iDeg' N (N*q^2) ⊤ ⊤ q A hq') φ
        = (q : ℤ) • heckeT N ⊤ q A φ) ∧
    (∀ φ, (jDeg N (N*q^2) ⊤ ⊤ q A hq').comp (iDeg' N (N*q^2) ⊤ ⊤ 1 A h1) φ
        = (q : ℤ) • heckeT N ⊤ q A φ) ∧
    (∀ φ, (jDeg N (N*q^2) ⊤ ⊤ q A hq').comp (iDeg' N (N*q^2) ⊤ ⊤ (q^2) A hq2) φ
        = (q : ℤ) • heckeT N ⊤ q A φ) ∧
    (∀ φ, (jDeg N (N*q^2) ⊤ ⊤ (q^2) A hq2).comp (iDeg' N (N*q^2) ⊤ ⊤ q A hq') φ
        = (q : ℤ) • heckeT N ⊤ q A φ) ∧
    (∀ φ, (jDeg N (N*q^2) ⊤ ⊤ 1 A h1).comp (iDeg' N (N*q^2) ⊤ ⊤ (q^2) A hq2) φ
        = (heckeT N ⊤ q A).comp (heckeT N ⊤ q A) φ - ((q : ℤ) + 1) • φ) ∧
    (∀ φ, (jDeg N (N*q^2) ⊤ ⊤ (q^2) A hq2).comp (iDeg' N (N*q^2) ⊤ ⊤ 1 A h1) φ
        = (heckeT N ⊤ q A).comp (heckeT N ⊤ q A) φ - ((q : ℤ) + 1) • φ) := by sorry
