-- Prove2me | Theorems.Thm_CohCarrier_heckeT_iDeg_interchange
-- name    : CohCarrier.heckeT_iDeg_interchange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/a9d1d226-2a38-5ec6-afbd-7611aa18ecd9
-- title:
--   Interchange of U_q with the degeneracy maps ι₁^*,ι_q^*
-- statement:
--   Fix natural numbers $N$ and $q$, both nonzero and with $Nq$ nonzero, and an additive commutative group $A$. Assume $q$ is prime and $q \nmid N$. Assume further two instances of the predicate `LevelLE`: the first, `h₁`, records that $N \mid Nq$, that $1 \mid (Nq)/N$, and that reduction modulo $N$ carries every unit of $\mathbb{Z}/Nq$ lying in $\top$ into $\top \le (\mathbb{Z}/N)^\times$; the second, `hq`, records the same with $1$ replaced by $q$, i.e. $q \mid (Nq)/N$. Let $\varphi$ be an element of `H1 N ⊤ A`, that is an additive homomorphism from the additivisation of $\Gamma_{\top}(N) = \Gamma_0(N) \le \mathrm{SL}(2,\mathbb{Z})$ to $A$. Here `heckeT M ⊤ ℓ A` is the operator on such homomorphisms obtained by transfer from the subgroup `GammaHUpper M ⊤ ℓ` along the conjugation homomorphism `conjL` into $\Gamma_0(M)$, and `iDeg' N (N*q) ⊤ ⊤ d A h` is precomposition with the homomorphism $\Gamma_0(Nq) \to \Gamma_0(N)$ given by conjugation by the lower-triangular matrix attached to $d$. The conclusion is the identity $$U_q\bigl(\iota_1^*\varphi\bigr) = \iota_1^*\bigl(T_q\varphi\bigr) - \iota_q^*\varphi$$ in `H1 (N*q) ⊤ A`, where $U_q$ is `heckeT (N*q) ⊤ q A`, $T_q$ is `heckeT N ⊤ q A`, and $\iota_1^*, \iota_q^*$ are the two maps `iDeg'` attached to `h₁` and `hq`.
--
--   This is the classical commutation relation between the Hecke operator at $q$ and the two degeneracy maps from level $N$ to level $Nq$, in the form $U_q \circ \iota_1^* = \iota_1^* \circ T_q - \iota_q^*$, here realised on homomorphisms out of $\Gamma_0$ via the transfer. It is used downstream in the combinations of Hecke operators that vanish on the image of the degeneracy maps ([`CohCarrier.heckeT_comb_eq_zero`](thm.html#CohCarrier.heckeT_comb_eq_zero), [`CohCarrier.heckeT_eq_smul_of_forall_mem_Gamma_apply_eq_zero`](thm.html#CohCarrier.heckeT_eq_smul_of_forall_mem_Gamma_apply_eq_zero)) and in the analysis of the corner maps at level $Nq^2$ ([`CohCarrier.jDeg_iDeg_corner_of_prime_sq`](thm.html#CohCarrier.jDeg_iDeg_corner_of_prime_sq)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_heckeT_iDeg_interchange.lean

import Definitions.Def_CohCarrier_Level

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CohCarrier.heckeT_iDeg_interchange {N q : ℕ} [NeZero N] [NeZero q] {A : Type} [AddCommGroup A] [NeZero (N * q)]
    (hqp : q.Prime) (hqN : ¬ q ∣ N)
    (h₁ : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) 1)
    (hq : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) q)
    (φ : H1 N ⊤ A) :
    heckeT (N * q) ⊤ q A (iDeg' N (N * q) ⊤ ⊤ 1 A h₁ φ)
      = iDeg' N (N * q) ⊤ ⊤ 1 A h₁ (heckeT N ⊤ q A φ)
          - iDeg' N (N * q) ⊤ ⊤ q A hq φ := by sorry
