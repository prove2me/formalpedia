-- Prove2me | Theorems.Thm_CohCarrier_heckeT_heckeT_eq_self_of_jDeg_one_eq_zero_of_jDeg_eq_zero
-- name    : CohCarrier.heckeT_heckeT_eq_self_of_jDeg_one_eq_zero_of_jDeg_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/bef5ba39-e2bb-5bae-aecd-889e9b020739
-- title:
--   Uᵣ is an involution on r-new classes
-- statement:
--   Fix natural numbers $N$ and $r$, both nonzero, with $r$ prime and $r \nmid N$, and an additive abelian group $A$. Here $\mathrm{H}^1(M,\top,A)$ denotes the group of additive homomorphisms from $\Gamma_H(M)$ with $H = \top$ — that is, from $\Gamma_0(M) \le \mathrm{SL}(2,\mathbb{Z})$, written additively — to $A$. Two instances of the predicate [`CohCarrier.LevelLE`](def/CohCarrier_Level.html#L330) are assumed, for the degrees $d = 1$ and $d = r$ respectively: each asserts $N \mid Nr$, that $d$ divides $(Nr)/N$, and that the reduction map on unit groups carries the chosen subgroup of $(\mathbb{Z}/Nr)^\times$ into that of $(\mathbb{Z}/N)^\times$ (both being the full subgroups here, so this last condition is automatic). Let $\varphi \colon \Gamma_0(Nr) \to A$ be a homomorphism and suppose that both degeneracy trace maps vanish on it: for $d = 1$ and $d = r$, [`CohCarrier.jDeg`](def/CohCarrier_Level.html#L482), the corestriction from the image of the degree-$d$ embedding `iotaDeg` of $\Gamma_0(Nr)$ into $\Gamma_0(N)$ up to $\Gamma_0(N)$ of the transported character, sends $\varphi$ to $0$. The conclusion is that applying [`CohCarrier.heckeT`](def/CohCarrier_Level.html#L250) at $\ell = r$ twice returns $\varphi$, where [`CohCarrier.heckeT`](def/CohCarrier_Level.html#L250) is the transfer to $\Gamma_0(Nr)$, along the subgroup $\Gamma_H^{\mathrm{upper}}(Nr,\top,r)$, of $\varphi$ composed with the conjugation homomorphism [`CohCarrier.conjL`](def/CohCarrier_Level.html#L228).
--
--   This is the cohomological form, with arbitrary abelian coefficients, of the theorem of Atkin and Lehner that the Hecke operator at a prime exactly dividing the level acts as an involution on the new part, equivalently that $a_r(f)^2 = 1$ for a newform of weight $2$ with $r \parallel M$. It is used by [`CohCarrier.eq_zero_of_mem_parabolicHoms_of_jDeg_eq_zero_of_apply_T_sq_ne`](thm.html#CohCarrier.eq_zero_of_mem_parabolicHoms_of_jDeg_eq_zero_of_apply_T_sq_ne) to force vanishing of a class whose $T_r$-square eigenvalue differs from $1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_heckeT_heckeT_eq_self_of_jDeg_one_eq_zero_of_jDeg_eq_zero.lean

import Definitions.Def_CohCarrier_Level

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CohCarrier.heckeT_heckeT_eq_self_of_jDeg_one_eq_zero_of_jDeg_eq_zero
    (N r : ℕ) [NeZero N] [NeZero r] (hr : r.Prime) (hrN : ¬ r ∣ N)
    (A : Type) [AddCommGroup A]

    (h₁ : CohCarrier.LevelLE N (N * r) ⊤ ⊤ 1) (hr' : CohCarrier.LevelLE N (N * r) ⊤ ⊤ r)

    (φ : CohCarrier.H1 (N * r) ⊤ A)
    (hφ₁ : CohCarrier.jDeg N (N * r) ⊤ ⊤ 1 A h₁ φ = 0)
    (hφr : CohCarrier.jDeg N (N * r) ⊤ ⊤ r A hr' φ = 0) :
    CohCarrier.heckeT (N * r) ⊤ r A (CohCarrier.heckeT (N * r) ⊤ r A φ) = φ := by sorry
