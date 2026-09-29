-- Prove2me | Theorems.Thm_CohCarrier_exists_atkinLehnerOp_iDegL_jDegL_five_identities_of_prime
-- name    : CohCarrier.exists_atkinLehnerOp_iDegL_jDegL_five_identities_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/f5614164-024f-5e61-a15f-5a33625faf81
-- title:
--   Atkin–Lehner operator at q: five degeneracy identities
-- statement:
--   Let $M$ and $q$ be non-zero naturals with $q$ prime and $q\nmid M$, let $H\le(\mathbb Z/M)^{\times}$ and $H'\le(\mathbb Z/Mq)^{\times}$ be subgroups such that a unit $v$ of $\mathbb Z/Mq$ lies in $H'$ exactly when its reduction lies in $H$, let `h1` witness `LevelLE M (M*q) H H' 1` (that is, $M\mid Mq$, $1\mid Mq/M$, and units of $H'$ reduce into $H$), and let $\mathcal O$ be a commutative ring. Writing $H^1(N,K,\mathcal O)$ for the $\mathcal O$-module of additive homomorphisms $\mathrm{Hom}(\Gamma_K(N),\mathcal O)$, with $\iota=$ `iDegL` the restriction along the degree-$1$ map `iotaDeg` of $\Gamma_{H'}(Mq)$ into $\Gamma_H(M)$, $j=$ `jDegL` the transfer in the opposite direction, $T_\ell=$ `heckeTL` (transfer from the upper congruence subgroup at $\ell$ composed with `conjL`) and $\langle\,\cdot\,\rangle=$ `diamondL`, the assertion is that there exist a unit $u$ of $\mathbb Z/Mq$ and an $\mathcal O$-linear endomorphism $w$ of $H^1(Mq,H',\mathcal O)$ with: the reduction $\bar u\in\mathbb Z/M$ satisfies $\bar u\,q=1$; $w\circ\iota=(\iota\circ T_q^{(M)}-T_q^{(Mq)}\circ\iota)\circ\langle\bar u\rangle$; $j\circ\iota=(q+1)\cdot\mathrm{id}$; $j\circ w\circ\iota=T_q^{(M)}\circ\langle\bar u\rangle$; $\iota\circ j=\mathrm{id}+T_q^{(Mq)}\circ w$; $w\circ w=\langle u\rangle$; and $w$ commutes with $T_\ell^{(Mq)}$ for every prime $\ell\neq q$ and with $\langle v\rangle$ for every unit $v$ of $\mathbb Z/Mq$.
--
--   This is the Atkin–Lehner lemma at a prime $q$ exactly dividing the level, in the setting of weight-two group cohomology with trivial coefficients for $\Gamma_H(M)\cap\Gamma_0(q)$: the operator $w$ plays the role of $w_q$, $w\circ\iota$ of the second degeneracy map, and the five identities are the interchange formula for $U_q$, the degree of the covering, the cross term of the degeneracy calculus, the trace identity, and $w_q^2=\langle u\rangle$. It is used in the construction of the comparison isomorphism at Taylor–Wiles level, via [`CuspForm.TWLevel.exists_linearEquiv_ML_HR_init_of_toML_diamondL_eq`](thm.html#CuspForm.TWLevel.exists_linearEquiv_ML_HR_init_of_toML_diamondL_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_exists_atkinLehnerOp_iDegL_jDegL_five_identities_of_prime.lean

import Definitions.Def_CohCarrier_Inst

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CohCarrier

theorem CohCarrier.exists_atkinLehnerOp_iDegL_jDegL_five_identities_of_prime
    (M q : ℕ) [NeZero M] [NeZero q] (hq : q.Prime) (hqM : ¬ q ∣ M)
    (H : Subgroup (ZMod M)ˣ) (H' : Subgroup (ZMod (M * q))ˣ)
    (hH' : ∀ v : (ZMod (M * q))ˣ, v ∈ H' ↔ ZMod.unitsMap (dvd_mul_right M q) v ∈ H)
    (h1 : CohCarrier.LevelLE M (M * q) H H' 1)
    (𝒪 : Type) [CommRing 𝒪] :
    haveI : NeZero (M * q) := ⟨mul_ne_zero (NeZero.ne M) (NeZero.ne q)⟩
    ∃ (u : (ZMod (M * q))ˣ) (w : Module.End 𝒪 (CohCarrier.H1 (M * q) H' 𝒪)),

      (ZMod.unitsMap (dvd_mul_right M q) u : ZMod M) * (q : ZMod M) = 1 ∧

      w ∘ₗ CohCarrier.iDegL M (M * q) H H' 1 𝒪 𝒪 h1 =
        (CohCarrier.iDegL M (M * q) H H' 1 𝒪 𝒪 h1 ∘ₗ CohCarrier.heckeTL M H 𝒪 q -
            CohCarrier.heckeTL (M * q) H' 𝒪 q ∘ₗ CohCarrier.iDegL M (M * q) H H' 1 𝒪 𝒪 h1) ∘ₗ
          CohCarrier.diamondL M H 𝒪 (ZMod.unitsMap (dvd_mul_right M q) u) ∧

      CohCarrier.jDegL M (M * q) H H' 1 𝒪 𝒪 h1 ∘ₗ CohCarrier.iDegL M (M * q) H H' 1 𝒪 𝒪 h1 =
        ((q : 𝒪) + 1) • LinearMap.id ∧

      CohCarrier.jDegL M (M * q) H H' 1 𝒪 𝒪 h1 ∘ₗ w ∘ₗ CohCarrier.iDegL M (M * q) H H' 1 𝒪 𝒪 h1 =
        CohCarrier.heckeTL M H 𝒪 q *
          CohCarrier.diamondL M H 𝒪 (ZMod.unitsMap (dvd_mul_right M q) u) ∧

      CohCarrier.iDegL M (M * q) H H' 1 𝒪 𝒪 h1 ∘ₗ CohCarrier.jDegL M (M * q) H H' 1 𝒪 𝒪 h1 =
        LinearMap.id + CohCarrier.heckeTL (M * q) H' 𝒪 q * w ∧

      w * w = CohCarrier.diamondL (M * q) H' 𝒪 u ∧

      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ≠ q →
        w * (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeTL (M * q) H' 𝒪 ℓ) =
          (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeTL (M * q) H' 𝒪 ℓ) * w) ∧
      (∀ v : (ZMod (M * q))ˣ,
        w * CohCarrier.diamondL (M * q) H' 𝒪 v = CohCarrier.diamondL (M * q) H' 𝒪 v * w) := by sorry
