-- Prove2me | Theorems.Thm_CohCarrier_heckeT_top_apply_eq_smul_of_isOfFinOrder
-- name    : CohCarrier.heckeT_top_apply_eq_smul_of_isOfFinOrder
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/ab0b7393-075d-5753-8893-1887f299311a
-- title:
--   T_ℓ acts by ℓ+1 at elements of finite order
-- statement:
--   Fix a positive integer $N$ and an additive commutative group $A$, and let $\ell$ be a prime not dividing $N$. Here [`CohCarrier.GammaH N ⊤`](def/CohCarrier_Level.html#L133) is the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ obtained by pulling back the full subgroup of $(\mathbb{Z}/N)^\times$ along the character `gamma0Units N` of $\Gamma_0(N)$ (which sends a matrix to the unit given by its lower right entry modulo $N$) and pushing the result forward along the inclusion of $\Gamma_0(N)$, so it is $\Gamma_0(N)$ itself; and [`CohCarrier.H1 N ⊤ A`](def/CohCarrier_Level.html#L162) is the group of additive homomorphisms from the additivisation of that group to $A$, i.e. of group homomorphisms $\Gamma_0(N) \to A$. For such a $\varphi$, the operator [`CohCarrier.heckeT N ⊤ ℓ A`](def/CohCarrier_Level.html#L250) sends $\varphi$ to the additive homomorphism obtained from the transfer of $\varphi$, viewed multiplicatively, precomposed with the homomorphism `conjL N ⊤ ℓ` from [`CohCarrier.GammaHUpper N ⊤ ℓ`](def/CohCarrier_Level.html#L210) to $\Gamma_0(N)$ given by the conjugation operation `conjUpperMat ℓ`. The assertion is that for every element $\gamma$ of $\Gamma_0(N)$ of finite order, the value of $T_\ell\varphi$ at $\gamma$ equals $(\ell+1)\cdot\varphi(\gamma)$.
--
--   This records the classical fact that the Hecke operator $T_\ell$ at a prime $\ell$ not dividing the level acts on the values of a homomorphism $\Gamma_0(N) \to A$ at torsion elements (namely $\pm 1$ and the elliptic elements of order $3$, $4$, $6$) simply by multiplication by the index $\ell+1$ of the relevant subgroup. It is used in the construction of Galois representations attached to eigensystems on $H^1$, via [`GaloisRep.exists_galoisRep_trace_eq_of_isEigensystemH1_one_of_ringHom`](thm.html#GaloisRep.exists_galoisRep_trace_eq_of_isEigensystemH1_one_of_ringHom), where the eigenvalue condition has to be controlled at torsion classes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_heckeT_top_apply_eq_smul_of_isOfFinOrder.lean

import Mathlib
import Definitions.Def_CohCarrier_Level

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CohCarrier.heckeT_top_apply_eq_smul_of_isOfFinOrder
    (N : ℕ) [NeZero N] (A : Type) [AddCommGroup A] (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
    (φ : CohCarrier.H1 N ⊤ A) (γ : ↥(CohCarrier.GammaH N ⊤)) (hγ : IsOfFinOrder γ) :
    (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeT N ⊤ ℓ A φ (Additive.ofMul γ)) =
      (ℓ + 1) • φ (Additive.ofMul γ) := by sorry
