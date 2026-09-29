-- Prove2me | Theorems.Thm_CohCarrier_heckeT_sub_smul_mem_parabolicHoms_gammaH_of_modEq_one
-- name    : CohCarrier.heckeT_sub_smul_mem_parabolicHoms_gammaH_of_modEq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/c1d39e59-f652-54f4-a90a-7ba936a1b7b7
-- title:
--   Hecke T_ℓ acts by ℓ+1 modulo parabolic homomorphisms
-- statement:
--   Fix a positive integer $N$ and a subgroup $H \le (\mathbb{Z}/N)^{\times}$, and let $\Gamma_H(N) =$ [`CohCarrier.GammaH N H`](def/CohCarrier_Level.html#L133) be the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ consisting of those matrices of $\Gamma_0(N)$ whose lower-right entry, reduced mod $N$ and viewed as a unit, lies in $H$. Let $A$ be an arbitrary abelian group and let $\varphi$ be an element of [`CohCarrier.H1 N H A`](def/CohCarrier_Level.html#L162), that is, an additive homomorphism from $\Gamma_H(N)$ (written additively) to $A$. Let $\ell$ be a nonzero natural number which is prime, does not divide $N$, and satisfies $\ell \equiv 1 \pmod N$. Let $T_\ell =$ [`CohCarrier.heckeT N H ℓ A`](def/CohCarrier_Level.html#L250) be the operator on such homomorphisms given by restricting $\varphi$ along the conjugation map [`CohCarrier.conjL`](def/CohCarrier_Level.html#L228) from `GammaHUpper N H ℓ` into $\Gamma_H(N)$ and then applying the group-theoretic transfer back up to $\Gamma_H(N)$. The assertion is that $T_\ell\varphi - (\ell+1)\cdot\varphi$ lies in [`ModularCurve.Period.parabolicHoms ℤ (CohCarrier.GammaH N H) A`](def/ModularCurve_PeriodMap.html#L62), i.e. it vanishes on every $\gamma \in \Gamma_H(N)$ whose matrix trace satisfies $\mathrm{tr}(\gamma)^2 = 4$.
--
--   This is the statement that the Hecke operator $T_\ell$ acts as multiplication by $\ell+1$ on the boundary quotient of $H^1(\Gamma_H(N), A) = \mathrm{Hom}(\Gamma_H(N), A)$ by its parabolic part, for primes $\ell \equiv 1 \pmod N$ not dividing $N$, with arbitrary coefficient group $A$; in particular $T_\ell$ preserves the parabolic submodule. It is used in the Eisenstein-versus-cuspidal analysis of Hecke modules built from group cohomology of $\Gamma_H(N)$, for instance in the identification of residual Hecke characters and of corner submodules. The proof cites the computation of the index $\ell+1$ of `GammaHUpper N H ℓ` in $\Gamma_H(N)$ and the normal form $\gamma = \pm\,\delta T^{h}\delta^{-1}$ for elements of trace square $4$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_heckeT_sub_smul_mem_parabolicHoms_gammaH_of_modEq_one.lean

import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_PeriodMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CohCarrier.heckeT_sub_smul_mem_parabolicHoms_gammaH_of_modEq_one
    (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) (A : Type*) [AddCommGroup A]
    (φ : CohCarrier.H1 N H A) (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓ1 : ℓ ≡ 1 [MOD N]) :
    CohCarrier.heckeT N H ℓ A φ - (ℓ + 1) • φ ∈
      ModularCurve.Period.parabolicHoms ℤ (CohCarrier.GammaH N H) A := by sorry
