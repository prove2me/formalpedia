-- Prove2me | Theorems.Thm_CohCarrier_heckeT_sub_smul_mem_parabolicHoms_of_forall_modEq_one
-- name    : CohCarrier.heckeT_sub_smul_mem_parabolicHoms_of_forall_modEq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/2fbdee99-5478-5764-a456-beac43f2ba90
-- title:
--   T_ℓ acts as ℓ+1 modulo parabolic homomorphisms
-- statement:
--   Let $N$ be a natural number and $A$ an arbitrary additive abelian group. Write $\Gamma =$ [`CohCarrier.GammaH N ⊤`](def/CohCarrier_Level.html#L133), the subgroup of $SL(2,\mathbb{Z})$ obtained by pushing forward along the inclusion of $\Gamma_0(N)$ the preimage of the full subgroup $\top \le (\mathbb{Z}/N)^\times$ under the character `gamma0Units`, i.e. all of $\Gamma_0(N)$; and let $\varphi$ be an element of [`CohCarrier.H1 N ⊤ A`](def/CohCarrier_Level.html#L162), that is, an additive homomorphism from the additivisation of $\Gamma$ to $A$. Let $\ell$ be a nonzero natural number that is prime, does not divide $N$, and satisfies $\ell \equiv 1 \pmod t$ for every natural number $t$ with $t^2 \mid N$. Then the difference between [`CohCarrier.heckeT N ⊤ ℓ A φ`](def/CohCarrier_Level.html#L250) — the image of $\varphi$ under the Hecke operator obtained by composing $\varphi$ with the conjugation homomorphism `conjL` from `GammaHUpper N ⊤ ℓ` to $\Gamma$ and then applying the group transfer back to $\Gamma$ — and the $(\ell+1)$-fold multiple $(\ell+1)\bullet\varphi$ lies in [`ModularCurve.Period.parabolicHoms ℤ (CohCarrier.GammaH N ⊤) A`](def/ModularCurve_PeriodMap.html#L62): that is, $T_\ell\varphi - (\ell+1)\varphi$ vanishes on every $\gamma \in \Gamma$ whose integral $2\times 2$ matrix has trace of square $4$ (trace $\pm 2$).
--
--   This is the integral, group-cohomological form of the classical statement that $T_\ell$ acts as $\ell+1$ on the boundary, equivalently Eisenstein, quotient $H^1(\Gamma_0(N),A)/H^1_{\mathrm{par}}$, under the congruence condition $\ell \equiv 1$ modulo every $t$ with $t^2 \mid N$; it holds for arbitrary coefficient groups, including torsion ones. It is used downstream in the analysis of maximal ideals of the Hecke algebra acting on parabolic classes, in the rank computation for the corner submodule of $H^1$ in the non-Eisenstein case, and in identifying Hecke residues with traces of Frobenius.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_heckeT_sub_smul_mem_parabolicHoms_of_forall_modEq_one.lean

import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_PeriodMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CohCarrier.heckeT_sub_smul_mem_parabolicHoms_of_forall_modEq_one
    (N : ℕ) (A : Type*) [AddCommGroup A] (φ : CohCarrier.H1 N ⊤ A)
    (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
    (hℓ1 : ∀ t : ℕ, t * t ∣ N → ℓ ≡ 1 [MOD t]) :
    CohCarrier.heckeT N ⊤ ℓ A φ - (ℓ + 1) • φ ∈
      ModularCurve.Period.parabolicHoms ℤ (CohCarrier.GammaH N ⊤) A := by sorry
