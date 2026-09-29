-- Prove2me | Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_exists_isHomogeneousVBasis_apply_eq_of_forall_isUnit
-- name    : CerednikDrinfeld.GradedCartierModuleData.exists_isHomogeneousVBasis_apply_eq_of_forall_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/06bc28de-f7eb-581e-923b-94f3f60bc9d6
-- title:
--   Lifting homogeneous V-bases along a unit-detecting base change
-- statement:
--   Fix a prime $p$ and commutative rings $S$, $B$ equipped with ring homomorphisms $jS, j$ from $\mathbb{Z}_{p^2} = W(\mathbb{F}_{p^2})$, and let $q : S \to B$ be a ring homomorphism that is surjective and detects units, in the sense that $q(s)$ being a unit in $B$ forces $s$ to be a unit in $S$. Let $DS$ and $D$ be graded Cartier module data over $S$ and over $B$ respectively, that is, modules $DS.M$, $D.M$ over the Witt vectors of the respective base, carrying additive operators $F$, $V$ and a Witt-linear $\varpi$ satisfying the usual Cartier relations together with a decomposition of the module as an internal direct sum of two pieces indexed by $\mathrm{Fin}\ 2$ that each of $F$, $V$, $\varpi$ shifts by one. Assume both are special, i.e. each admits a homogeneous $V$-basis (a pair $\gamma_i$ in the $i$-th piece such that every element is uniquely $\sum_i [c_i]\gamma_i + V y$ with $c \in B^2$, resp. $S^2$, Teichmüller coefficients, and $y$ in the module) and each is $V$-adically complete. Let $f : DS.M \to D.M$ be additive and a base change along $q$: semilinear for $W(q)$, commuting with $F$, $V$ and $\varpi$, preserving the pieces, and carrying some homogeneous $V$-basis of $DS$ to a homogeneous $V$-basis of $D$. Then for every homogeneous $V$-basis $\beta$ of $D$ there is a homogeneous $V$-basis $\gamma$ of $DS$ with $f(\gamma_i) = \beta_i$ for $i = 0, 1$.
--
--   This is the Nakayama-type basis-lifting step for special graded Cartier modules: modulo $V$ the module is free of rank two on Teichmüller coefficients, and the unit-detecting hypothesis on $q$ lets a change of basis over $B$ be lifted to one over $S$. It is used to normalise bases of two lifts so that canonical maps can be compared, and is cited in the results on canonical $L$-maps [`CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.apply_comp_eq_nMap_apply_of_torsionFree`](thm.html#CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.apply_comp_eq_nMap_apply_of_torsionFree) and [`CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.eq_of_isNilpotent`](thm.html#CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.eq_of_isNilpotent).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_GradedCartierModuleData_exists_isHomogeneousVBasis_apply_eq_of_forall_isUnit.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CerednikDrinfeld.GradedCartierModuleData.exists_isHomogeneousVBasis_apply_eq_of_forall_isUnit
    (p : ℕ) [Fact p.Prime] {S B : Type} [CommRing S] [CommRing B]
    {jS : CerednikDrinfeld.Zp2 p →+* S} {j : CerednikDrinfeld.Zp2 p →+* B}
    (q : S →+* B) (hq : Function.Surjective q) (hu : ∀ s : S, IsUnit (q s) → IsUnit s)
    (DS : CerednikDrinfeld.GradedCartierModuleData p S jS) (hDS : DS.IsSpecialCartierModule)
    (D : CerednikDrinfeld.GradedCartierModuleData p B j) (hD : D.IsSpecialCartierModule)
    (f : DS.M →+ D.M) (hf : CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong' q DS D f)
    (β : Fin 2 → D.M) (hβ : D.IsHomogeneousVBasis β) :
    ∃ γ : Fin 2 → DS.M, DS.IsHomogeneousVBasis γ ∧ ∀ i : Fin 2, f (γ i) = β i := by sorry
