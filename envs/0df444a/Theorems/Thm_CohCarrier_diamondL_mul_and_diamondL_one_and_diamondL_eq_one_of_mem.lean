-- Prove2me | Theorems.Thm_CohCarrier_diamondL_mul_and_diamondL_one_and_diamondL_eq_one_of_mem
-- name    : CohCarrier.diamondL_mul_and_diamondL_one_and_diamondL_eq_one_of_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/02ea08c4-9caa-5e29-a870-3e966eab61dc
-- title:
--   Diamond operators are multiplicative, unital and trivial on H
-- statement:
--   Fix a natural number $M$ with $M \neq 0$, a subgroup $H$ of $(\mathbb{Z}/M)^{\times}$, and a commutative ring $\mathcal{O}$. For $d \in (\mathbb{Z}/M)^{\times}$, the operator [`CohCarrier.diamondL M H 𝒪 d`](def/CohCarrier_Inst.html#L55) is the $\mathcal{O}$-linear endomorphism of [`CohCarrier.H1 M H 𝒪`](def/CohCarrier_Level.html#L162) — the module of additive homomorphisms from `Additive (CohCarrier.GammaH M H)` to $\mathcal{O}$ — sending $\varphi$ to the composite of $\varphi$ with the additive form of the conjugation homomorphism [`CohCarrier.conjHom M H σ`](def/CohCarrier_Level.html#L284) of [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133), where $\sigma \in \Gamma_0(M)$ is a chosen element with [`CohCarrier.gamma0Units M σ = d`](def/CohCarrier_Level.html#L121), such a $\sigma$ existing by [`CohCarrier.gamma0Units_surjective`](def/CohCarrier_Inst.html#L39). The theorem asserts the conjunction of three statements: first, for all $u, v \in (\mathbb{Z}/M)^{\times}$ one has `diamondL M H 𝒪 (u * v) = diamondL M H 𝒪 u * diamondL M H 𝒪 v`, the product in the endomorphism ring being composition; second, `diamondL M H 𝒪 1` is the identity endomorphism; third, for every $u \in H$, `diamondL M H 𝒪 u` is the identity endomorphism. The three clauses are asserted as a conjunction of equalities of linear maps, not packaged as a monoid homomorphism from $(\mathbb{Z}/M)^{\times}/H$.
--
--   This is the statement that the diamond operators on $H^1(\Gamma_H(M), \mathcal{O}) = \operatorname{Hom}(\Gamma_H(M), \mathcal{O})$ define an action of $(\mathbb{Z}/M)^{\times}$ which is trivial on $H$, hence factors through $(\mathbb{Z}/M)^{\times}/H$ and in particular consists of commuting invertible operators. It is used in the analysis of the corner submodule and of degeneracy maps, for instance by [`CohCarrier.diamondL_apply_eq_self_of_mem_cornerSubmodule_of_sub_one_mem`](thm.html#CohCarrier.diamondL_apply_eq_self_of_mem_cornerSubmodule_of_sub_one_mem) and [`CohCarrier.cornerSubmodule_sigmaCorner_gammaH_eq_map_iDegL_one_of_isUnit_index`](thm.html#CohCarrier.cornerSubmodule_sigmaCorner_gammaH_eq_map_iDegL_one_of_isUnit_index).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_diamondL_mul_and_diamondL_one_and_diamondL_eq_one_of_mem.lean

import Definitions.Def_CohCarrier_Inst

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem CohCarrier.diamondL_mul_and_diamondL_one_and_diamondL_eq_one_of_mem
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (𝒪 : Type) [CommRing 𝒪] :
    (∀ u v : (ZMod M)ˣ, CohCarrier.diamondL M H 𝒪 (u * v) =
        CohCarrier.diamondL M H 𝒪 u * CohCarrier.diamondL M H 𝒪 v) ∧
    CohCarrier.diamondL M H 𝒪 1 = 1 ∧
    (∀ u ∈ H, CohCarrier.diamondL M H 𝒪 u = 1) := by sorry
