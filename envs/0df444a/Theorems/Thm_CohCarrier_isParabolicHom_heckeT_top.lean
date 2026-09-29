-- Prove2me | Theorems.Thm_CohCarrier_isParabolicHom_heckeT_top
-- name    : CohCarrier.isParabolicHom_heckeT_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/e79c17b3-f71f-50ec-a6fc-583326b60edc
-- title:
--   The transfer Hecke operator T_ℓ preserves parabolic homomorphisms
-- statement:
--   Let $N$ and $\ell$ be natural numbers with $\ell \neq 0$, and let $A$ be an additive abelian group. Write $\Gamma_H(N,\top)$ for the subgroup [`CohCarrier.GammaH N ⊤`](def/CohCarrier_Level.html#L133) of $\mathrm{SL}_2(\mathbb{Z})$, that is, the image under the inclusion of $\Gamma_0(N)$ of the preimage of the full subgroup $\top \le (\mathbb{Z}/N)^\times$ under the homomorphism $\Gamma_0(N) \to (\mathbb{Z}/N)^\times$ sending $\gamma$ to the class of its lower-right entry; thus $\Gamma_H(N,\top)$ is all of $\Gamma_0(N)$. Let $\varphi$ be an element of [`CohCarrier.H1 N ⊤ A`](def/CohCarrier_Level.html#L162), i.e. a homomorphism from the additivisation of $\Gamma_H(N,\top)$ to $A$, and suppose $\varphi$ is parabolic in the sense of [`ModularCurve.Period.IsParabolicHom`](def/ModularCurve_PeriodMap.html#L15): $\varphi(\gamma) = 0$ for every $\gamma \in \Gamma_H(N,\top)$ whose underlying integral matrix has $(\operatorname{tr}\gamma)^2 = 4$. Then the image $T_\ell\varphi =$ [`CohCarrier.heckeT N ⊤ ℓ A φ`](def/CohCarrier_Level.html#L250), defined as the group transfer of $\varphi$ precomposed with the conjugation map [`CohCarrier.conjL`](def/CohCarrier_Level.html#L228) from $\Gamma_H(N,\top) \cap \Gamma^0(\ell)$ into $\Gamma_H(N,\top)$, is again parabolic: it vanishes on every element of $\Gamma_H(N,\top)$ of trace $\pm 2$.
--
--   This records that the transfer-defined Hecke operator $T_\ell$ at trivial nebentypus acts on the parabolic part of $H^1(\Gamma_0(N), A) = \operatorname{Hom}(\Gamma_0(N), A)$, so that the parabolic subgroup is stable under the Hecke algebra; no primality or coprimality assumption on $\ell$ is made, so the case $\ell \mid N$ (the operator usually written $U_\ell$) is included. It is used in the construction of a perfect self-adjoint pairing on parabolic homomorphisms, [`CohCarrier.exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms`](thm.html#CohCarrier.exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_isParabolicHom_heckeT_top.lean

import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_PeriodMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CohCarrier.isParabolicHom_heckeT_top (N ℓ : ℕ) [NeZero ℓ] (A : Type*) [AddCommGroup A]
    (φ : CohCarrier.H1 N ⊤ A) (hφ : ModularCurve.Period.IsParabolicHom (CohCarrier.GammaH N ⊤) φ) :
    ModularCurve.Period.IsParabolicHom (CohCarrier.GammaH N ⊤) (CohCarrier.heckeT N ⊤ ℓ A φ) := by sorry
