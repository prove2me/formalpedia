-- Prove2me | Theorems.Thm_CohCarrier_heckeT_heckeTlower_eq_add_smul_iDeg_jDeg_of_prime
-- name    : CohCarrier.heckeT_heckeTlower_eq_add_smul_iDeg_jDeg_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/27ed16a7-f959-58f4-afab-dd02aa53f3f1
-- title:
--   Hecke relation U_q U_q^∨ = 1+(q-1)ι^*j at q ∥ Mq
-- statement:
--   Fix natural numbers $M$ and $q$, both nonzero, and an additive abelian group $A$; assume $q$ is prime and $q \nmid M$. Assume moreover `LevelLE M (M * q) ⊤ ⊤ 1`, i.e. $M \mid Mq$, $1 \mid (Mq)/M$, and every unit of $\mathbb{Z}/Mq$ lying in the full subgroup reduces into the full subgroup of $(\mathbb{Z}/M)^\times$. Here `H1 N ⊤ A` is the group of additive homomorphisms from `Additive (GammaH N ⊤)` to $A$, that is, homomorphisms $\Gamma_0(N)\to A$ for the image in $SL_2(\mathbb{Z})$ of the preimage of the full unit subgroup under `gamma0Units N`. For $\varphi \in$ `H1 (M * q) ⊤ A` the conclusion asserts the identity $$\mathrm{heckeT}\bigl(\mathrm{heckeTlower}(\varphi)\bigr) = \varphi + (q-1)\cdot \mathrm{iDeg}'\bigl(\mathrm{jDeg}(\varphi)\bigr),$$ where `heckeTlower (M*q) ⊤ q A` is the transfer to $\Gamma_0(Mq)$ of $\varphi$ precomposed with the conjugation `conjLowerL` of the subgroup `GammaHLower (M*q) ⊤ q` by the lower matrix at $q$, `heckeT (M*q) ⊤ q A` is the transfer of $\varphi$ precomposed with the conjugation `conjL` of `GammaHUpper (M*q) ⊤ q` by the upper matrix at $q$, `jDeg M (M*q) ⊤ ⊤ 1 A h1` is the transfer along the map `iotaDeg` with $d = 1$ (the inclusion $\Gamma_0(Mq)\le\Gamma_0(M)$), and `iDeg' M (M*q) ⊤ ⊤ 1 A h1` is precomposition with that same inclusion; the coefficient $q-1$ is truncated subtraction in $\mathbb{N}$ acting on $A$-valued homomorphisms.
--
--   This is the quadratic relation of the Iwahori–Hecke algebra at a prime $q$ exactly dividing the level, in the form $U_q U_q^\vee = 1 + (q-1)\,\iota^{*} j$ on homomorphisms from $\Gamma_0(Mq)$, the two Hecke operators being the transfers attached to the double cosets of $\mathrm{diag}(1,q)$ and $\mathrm{diag}(q,1)$ and $\iota^{*}, j$ the restriction and transfer for $\Gamma_0(Mq)\le\Gamma_0(M)$ of index $q+1$. It is used in the local Hecke analysis at $q$, in the construction of corner realisations and rungs.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_heckeT_heckeTlower_eq_add_smul_iDeg_jDeg_of_prime.lean

import Definitions.Def_CohCarrier_Lower

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CohCarrier in

theorem CohCarrier.heckeT_heckeTlower_eq_add_smul_iDeg_jDeg_of_prime (M q : ℕ) [NeZero M]
    [NeZero q] (A : Type) [AddCommGroup A] (hq : q.Prime) (hqM : ¬ q ∣ M)
    (h1 : LevelLE M (M * q) (⊤ : Subgroup (ZMod M)ˣ) (⊤ : Subgroup (ZMod (M * q))ˣ) 1)
    (φ : H1 (M * q) ⊤ A) :
    heckeT (M * q) ⊤ q A (heckeTlower (M * q) ⊤ q A φ)
      = φ + (q - 1) • iDeg' M (M * q) ⊤ ⊤ 1 A h1 (jDeg M (M * q) ⊤ ⊤ 1 A h1 φ) := by sorry
