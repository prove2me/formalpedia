-- Prove2me | Theorems.Thm_CerednikDrinfeld_Mumford_invariantFieldOf_sup_map_conj_eq_inf_and_relfinrank_eq_relIndex
-- name    : CerednikDrinfeld.Mumford.invariantFieldOf_sup_map_conj_eq_inf_and_relfinrank_eq_relIndex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/03fc009a-f1b7-54f4-85a6-002b98a6f6fb
-- title:
--   Compositum of invariant fields of Γ and sΓ s⁻¹
-- statement:
--   Let $K$ be a field, $G$ a group and $M$ a commutative $K$-algebra that is a domain, with $G$ acting on $M$ by ring automorphisms in a way compatible with the $K$-scalars, so that $G$ acts on $\operatorname{Frac} M$; for a subgroup $\Delta\le G$ write $\mathfrak M(\Delta)$ for `invariantFieldOf K G M Δ`, the subfield of $\operatorname{Frac} M$ consisting of those $x$ with $\gamma\cdot x=x$ for all $\gamma\in\Delta$. Fix a subgroup $\Gamma\le G$, an element $s\in G$, and write $s\Gamma s^{-1}$ for the image of $\Gamma$ under conjugation by $s$. Assume given a subgroup $N$ with $N\le \Gamma\cap s\Gamma s^{-1}$, such that $\gamma n\gamma^{-1}\in N$ for all $\gamma\in\Gamma$, $n\in N$, and such that the relative index of $N$ in $\Gamma$ is non-zero (i.e. $[\Gamma:\Gamma\cap N]$ is finite). Assume moreover (F1) every $\gamma\in\Gamma$ acting trivially on all of $\mathfrak M(N)$ lies in $N$, and (F2) for every $\gamma\in\Gamma$, if $s^{-1}\gamma s$ acts trivially on all of $\mathfrak M(\Gamma)$ then $s^{-1}\gamma s\in\Gamma$. Then the join of the subfields $\mathfrak M(\Gamma)$ and $\mathfrak M(s\Gamma s^{-1})$ equals $\mathfrak M(\Gamma\cap s\Gamma s^{-1})$, and the relative finrank of $\mathfrak M(\Gamma\cap s\Gamma s^{-1})$ over $\mathfrak M(\Gamma)$ equals the relative index of $\Gamma\cap s\Gamma s^{-1}$ in $\Gamma$.
--
--   This is the Artin-style fixed-field statement underlying the comparison of an invariant function field with the invariant field of a conjugate subgroup: the compositum is the invariant field of the intersection, and the degree equals the corresponding group index, as for the degrees of Hecke correspondences on quotients. It is used in the Čerednik–Drinfeld part of the development, where [`CerednikDrinfeld.descentIntertwining_of_base_one_zero`](thm.html#CerednikDrinfeld.descentIntertwining_of_base_one_zero) and [`CerednikDrinfeld.descentIntertwining_of_base_zero_one`](thm.html#CerednikDrinfeld.descentIntertwining_of_base_zero_one) invoke it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Mumford_invariantFieldOf_sup_map_conj_eq_inf_and_relfinrank_eq_relIndex.lean

import Mathlib.FieldTheory.Relrank
import Definitions.Def_CerednikDrinfeld_MumfordQuotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.Mumford.invariantFieldOf_sup_map_conj_eq_inf_and_relfinrank_eq_relIndex
    (K : Type) [Field K] (G : Type) [Group G] (M : Type) [CommRing M] [Algebra K M]
    [MulSemiringAction G M] [SMulCommClass G K M] [IsDomain M]
    (Γ : Subgroup G) (s : G)
    (N : Subgroup G) (hN : N ≤ Γ ⊓ Γ.map (MulAut.conj s).toMonoidHom)
    (hNΓ : ∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N)
    (hfin : N.relIndex Γ ≠ 0)
    (hF1 : ∀ γ ∈ Γ, (∀ x ∈ invariantFieldOf K G M N, γ • x = x) → γ ∈ N)
    (hF2 : ∀ γ ∈ Γ, (∀ x ∈ invariantFieldOf K G M Γ, (s⁻¹ * γ * s) • x = x) → s⁻¹ * γ * s ∈ Γ) :
    invariantFieldOf K G M Γ ⊔ invariantFieldOf K G M (Γ.map (MulAut.conj s).toMonoidHom) =
        invariantFieldOf K G M (Γ ⊓ Γ.map (MulAut.conj s).toMonoidHom) ∧
      Subfield.relfinrank (invariantFieldOf K G M Γ) (invariantFieldOf K G M (Γ ⊓ Γ.map (MulAut.conj s).toMonoidHom)) =
        (Γ ⊓ Γ.map (MulAut.conj s).toMonoidHom).relIndex Γ := by sorry
