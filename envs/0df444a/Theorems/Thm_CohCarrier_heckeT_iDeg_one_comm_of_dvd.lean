-- Prove2me | Theorems.Thm_CohCarrier_heckeT_iDeg_one_comm_of_dvd
-- name    : CohCarrier.heckeT_iDeg_one_comm_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/ac977f06-34ef-5f40-9a74-21594d8252c5
-- title:
--   U_q commutes with the degree-one degeneracy map
-- statement:
--   Let $N$ and $q$ be natural numbers with $q$ and $N\cdot q$ nonzero, let $A$ be an additive commutative group, and write $\Gamma_{\top}(M)$ for `GammaH M ⊤`, the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ obtained as the image of $\Gamma_0(M)$ under the preimage of the full subgroup of $(\mathbb{Z}/M)^\times$ along `gamma0Units M`; thus `H1 M ⊤ A` is the group of additive homomorphisms from the additivisation of $\Gamma_{\top}(M)$ to $A$. Assume given $h_1$ : `LevelLE N (N*q) ⊤ ⊤ 1`, that is, $N \mid N\cdot q$, $1 \mid (N\cdot q)/N$, and the (vacuous, for the full subgroup) condition that units of $\mathbb{Z}/(N\cdot q)$ in $\top$ reduce into $\top$; assume also $q \mid N$, and let $\varphi \in$ `H1 N ⊤ A`. The degeneracy map `iDeg'` at parameter $1$ is precomposition with the homomorphism $\Gamma_{\top}(N\cdot q) \to \Gamma_{\top}(N)$ given by `conjLowerMat 1`, and `heckeT M ⊤ ℓ A` is the operator obtained by transferring $\varphi$, viewed multiplicatively, along `conjL M ⊤ ℓ` from `GammaHUpper M ⊤ ℓ` to $\Gamma_{\top}(M)$. The assertion is that applying `heckeT (N*q) ⊤ q A` to the image of $\varphi$ under `iDeg'` gives the same element of `H1 (N*q) ⊤ A` as applying `iDeg'` to `heckeT N ⊤ q A φ`.
--
--   This is the commutation of the Hecke operator $U_q$ at a prime-to-nothing divisor $q$ of the level with the degree-one degeneracy map $\mathrm{H}^1(\Gamma_0(N)) \to \mathrm{H}^1(\Gamma_0(Nq))$, in the cohomological (transfer) model of Hecke operators used here. It is used in the level-raising part of the development, by [`CohCarrier.heckeT_comb_eq_zero`](thm.html#CohCarrier.heckeT_comb_eq_zero), [`CohCarrier.levelRaisingComb_mem_cornerSubmodule_of_prime_of_dvd`](thm.html#CohCarrier.levelRaisingComb_mem_cornerSubmodule_of_prime_of_dvd) and [`CohCarrier.exists_idempotentSplitting_algHom_apply_toCornerRing_eq_level_mul_of_prime_of_dvd`](thm.html#CohCarrier.exists_idempotentSplitting_algHom_apply_toCornerRing_eq_level_mul_of_prime_of_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_heckeT_iDeg_one_comm_of_dvd.lean

import Definitions.Def_CohCarrier_Level

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CohCarrier.heckeT_iDeg_one_comm_of_dvd {N q : ℕ} [NeZero q] {A : Type} [AddCommGroup A] [NeZero (N * q)]
    (h₁ : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) 1)
    (hqN : q ∣ N) (φ : H1 N ⊤ A) :
    heckeT (N * q) ⊤ q A (iDeg' N (N * q) ⊤ ⊤ 1 A h₁ φ)
      = iDeg' N (N * q) ⊤ ⊤ 1 A h₁ (heckeT N ⊤ q A φ) := by sorry
