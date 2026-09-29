-- Prove2me | Theorems.Thm_CohCarrier_exists_squarefree_aeval_heckeTL_eq_zero_of_complex
-- name    : CohCarrier.exists_squarefree_aeval_heckeTL_eq_zero_of_complex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/a951ea58-d0d8-59d9-89fe-a12e31cc1007
-- title:
--   Descent to ℚ of a squarefree annihilator of T_ℓ
-- statement:
--   Fix an integer $M \ge 1$ (a `NeZero M` instance), a subgroup $H \le (\mathbb{Z}/M)^\times$, and an integer $\ell \ge 1$. For a commutative ring $\mathcal{O}$, the module [`CohCarrier.H1 M H 𝒪`](def/CohCarrier_Level.html#L162) consists of additive maps on `Additive ↥(GammaH M H)`, i.e. of $\mathcal{O}$-valued characters of the congruence group $\Gamma_H(M)$, and [`CohCarrier.heckeTL M H 𝒪 ℓ`](def/CohCarrier_Inst.html#L23) is the $\mathcal{O}$-linear endomorphism of it sending $\varphi$ to the transfer (corestriction) from the finite-index subgroup `GammaHUpper M H ℓ` of $\Gamma_H(M)$ up to $\Gamma_H(M)$ of the character obtained by restricting $\varphi$ along the homomorphism `conjL M H ℓ`, conjugation by the upper-triangular matrix `conjUpperMat ℓ`, which carries `GammaHUpper M H ℓ` into $\Gamma_H(M)$. The hypothesis is that there exists a squarefree $p \in \mathbb{C}[X]$ with $p$ evaluated at `heckeTL M H ℂ ℓ` equal to $0$. The conclusion is that for every field $K$ of characteristic zero there exists a squarefree $p \in K[X]$ whose evaluation at `heckeTL M H K ℓ` is $0$.
--
--   The statement transports semisimplicity of the transfer Hecke operator $T_\ell$ acting on characters of $\Gamma_H(M)$, expressed as the existence of a squarefree annihilating polynomial, from coefficients $\mathbb{C}$ to an arbitrary field of characteristic zero; it involves no modular input beyond the structure of the operator. It is used by [`CohCarrier.exists_squarefree_aeval_heckeTL_eq_zero`](thm.html#CohCarrier.exists_squarefree_aeval_heckeTL_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_exists_squarefree_aeval_heckeTL_eq_zero_of_complex.lean

import Mathlib
import Definitions.Def_CohCarrier_Inst

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CohCarrier.exists_squarefree_aeval_heckeTL_eq_zero_of_complex
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ]
    (h : ∃ p : Polynomial ℂ, Squarefree p ∧ Polynomial.aeval (CohCarrier.heckeTL M H ℂ ℓ) p = 0)
    (K : Type) [Field K] [CharZero K] :
    ∃ p : Polynomial K, Squarefree p ∧ Polynomial.aeval (CohCarrier.heckeTL M H K ℓ) p = 0 := by sorry
