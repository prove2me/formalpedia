-- Prove2me | Theorems.Thm_CohCarrier_diamondRaw_comm
-- name    : CohCarrier.diamondRaw_comm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/944c6640-2dbf-57be-ae7c-7564f178eb74
-- title:
--   Diamond operators on Hom(Γ_H(M),V) commute
-- statement:
--   Fix a natural number $M$, a subgroup $H \le (\mathbb{Z}/M\mathbb{Z})^{\times}$ and two elements $\sigma,\sigma'$ of the congruence subgroup $\Gamma_0(M) \le \mathrm{SL}_2(\mathbb{Z})$. Write $\Gamma_H(M)$ for the subgroup `GammaH M H` of $\mathrm{SL}_2(\mathbb{Z})$, namely the image in $\mathrm{SL}_2(\mathbb{Z})$ of the preimage of $H$ under the character `gamma0Units M` of $\Gamma_0(M)$. Let $V$ be an additive abelian group and let $F$ be an element of `H1 M H V`, that is an additive homomorphism from the additivisation of $\Gamma_H(M)$ to $V$ (equivalently, a group homomorphism $\Gamma_H(M) \to V$). For $\sigma \in \Gamma_0(M)$ the operator `diamondRaw M H V σ` sends such an $F$ to its precomposition with the endomorphism $\gamma \mapsto \sigma\gamma\sigma^{-1}$ of $\Gamma_H(M)$, which is well defined since $\Gamma_H(M)$ is normalised by $\Gamma_0(M)$. The assertion is that these two operators commute on $F$: applying `diamondRaw M H V σ` after `diamondRaw M H V σ'` gives the same homomorphism as applying them in the opposite order.
--
--   This is the commutativity of the raw diamond (conjugation) action of $\Gamma_0(M)$ on homomorphisms out of $\Gamma_H(M)$, the group-theoretic shadow of the fact that the diamond operators $\langle d\rangle$ commute; it reflects the triviality of inner automorphisms of $\Gamma_H(M)$ on abelian-valued homomorphisms. It feeds the commutativity of the family of operators built on this carrier, [`CohCarrier.opFamily_comm`](thm.html#CohCarrier.opFamily_comm), and thence the Hecke-algebra statements about cusp forms used later in the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_diamondRaw_comm.lean

import Definitions.Def_CohCarrier_Level

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CohCarrier.diamondRaw_comm (M : ℕ) (H : Subgroup (ZMod M)ˣ) (σ σ' : CongruenceSubgroup.Gamma0 M)
    {V : Type} [AddCommGroup V] (F : H1 M H V) :
    diamondRaw M H V σ (diamondRaw M H V σ' F) = diamondRaw M H V σ' (diamondRaw M H V σ F) := by sorry
