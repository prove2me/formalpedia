-- Prove2me | Theorems.Thm_CohCarrier_exists_squarefree_aeval_heckeTL_eq_zero
-- name    : CohCarrier.exists_squarefree_aeval_heckeTL_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/743025af-eea6-5b58-a117-4b16c8b7e8ab
-- title:
--   A squarefree polynomial annihilates T_ℓ on H¹
-- statement:
--   Fix a natural number $M$, nonzero, a subgroup $H \le (\mathbb{Z}/M)^\times$, and a natural number $\ell$, nonzero, which is prime and does not divide $M$; let $K$ be a field of characteristic zero. The operator in question is [`CohCarrier.heckeTL M H K ℓ`](def/CohCarrier_Inst.html#L23), the $K$-linear endomorphism of the cohomology carrier [`CohCarrier.H1 M H K`](def/CohCarrier_Level.html#L162) which sends a class $\varphi$ to the additive corestriction (transfer) `coresAdd` along the finite-index inclusion of [`CohCarrier.GammaHUpper M H ℓ`](def/CohCarrier_Level.html#L210) of the pullback of $\varphi$ by the additivisation of the group homomorphism [`CohCarrier.conjL M H ℓ`](def/CohCarrier_Level.html#L228), the latter mapping a matrix $\gamma$ in `GammaHUpper M H ℓ` to its conjugate `conjUpperMat ℓ γ` in [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133); thus $T_\ell$ is the composite of conjugation by the relevant upper-triangular matrix with transfer back to the full level group. The assertion is that there exists a polynomial $p \in K[X]$ which is squarefree and for which the evaluation $p(T_\ell)$, taken in the $K$-algebra of endomorphisms of [`CohCarrier.H1 M H K`](def/CohCarrier_Level.html#L162), is the zero endomorphism. Equivalently, $T_\ell$ is annihilated by a squarefree polynomial, i.e. it is a semisimple endomorphism of this $K$-module.
--
--   This is the semisimplicity (diagonalisability over $\bar K$) of the Hecke operator $T_\ell$ for $\ell \nmid M$ acting on the group cohomology $H^1(\Gamma_H(M), K)$ in characteristic zero. It is used to show that the relevant Hecke ring of weight-two forms of the given level is reduced, via [`CuspForm.TWLevel.HeckeRing.isReduced`](thm.html#CuspForm.TWLevel.HeckeRing.isReduced).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_exists_squarefree_aeval_heckeTL_eq_zero.lean

import Mathlib
import Definitions.Def_CohCarrier_Inst

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CohCarrier.exists_squarefree_aeval_heckeTL_eq_zero
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M)
    (K : Type) [Field K] [CharZero K] :
    ∃ p : Polynomial K, Squarefree p ∧ Polynomial.aeval (CohCarrier.heckeTL M H K ℓ) p = 0 := by sorry
