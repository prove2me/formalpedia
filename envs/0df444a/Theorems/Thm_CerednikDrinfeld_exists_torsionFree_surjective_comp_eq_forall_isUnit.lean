-- Prove2me | Theorems.Thm_CerednikDrinfeld_exists_torsionFree_surjective_comp_eq_forall_isUnit
-- name    : CerednikDrinfeld.exists_torsionFree_surjective_comp_eq_forall_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/3e657a2a-6158-52f0-8efb-b970f0e4dd7a
-- title:
--   Unit-reflecting p-torsion-free factorisation of a ring surjection
-- statement:
--   Let $p$ be a natural number, let $S$ and $B$ be commutative rings, and let $q\colon S\to B$ be a ring homomorphism. Assume $q$ is surjective and that $S$ has no $p$-torsion in the sense that $(p\cdot 1_S)\,s=0$ implies $s=0$ for all $s\in S$. The conclusion asserts the existence of a commutative ring $S'$ together with ring homomorphisms $\iota\colon S\to S'$ and $q'\colon S'\to B$ such that: $S'$ again has no $p$-torsion, i.e. $(p\cdot 1_{S'})\,s=0$ implies $s=0$ for all $s\in S'$; $q'$ is surjective; the composite $\iota$ followed by $q'$ equals $q$; and $q'$ reflects units, i.e. for every $s\in S'$, if $q'(s)$ is a unit of $B$ then $s$ is a unit of $S'$. No hypothesis of finiteness, noetherianity or locality is imposed, and no compatibility beyond $q'\circ\iota=q$ is claimed; in particular $\iota$ is not asserted to be injective. Both $S$ and $B$, and hence $S'$, are taken in the base universe.
--
--   This is the localisation step which upgrades a surjection of $p$-torsion-free rings to one whose source detects invertibility in the target, so that entrywise lifts of invertible matrices over $B$ are automatically invertible over $S'$. It is used in the Čerednik–Drinfeld part of the development, where homogeneous $V$-bases of graded Cartier module data must be matched along base change: it is cited by [`CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.apply_comp_eq_nMap_apply_of_torsionFree`](thm.html#CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.apply_comp_eq_nMap_apply_of_torsionFree) and by [`CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.eq_of_isNilpotent`](thm.html#CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.eq_of_isNilpotent).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_exists_torsionFree_surjective_comp_eq_forall_isUnit.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CerednikDrinfeld.exists_torsionFree_surjective_comp_eq_forall_isUnit
    (p : ℕ) {S B : Type} [CommRing S] [CommRing B]
    (q : S →+* B) (hq : Function.Surjective q) (hS : ∀ s : S, (p : S) * s = 0 → s = 0) :
    ∃ (S' : Type) (_ : CommRing S') (ι : S →+* S') (q' : S' →+* B),
      (∀ s : S', (p : S') * s = 0 → s = 0) ∧ Function.Surjective q' ∧ q'.comp ι = q ∧
      ∀ s : S', IsUnit (q' s) → IsUnit s := by sorry
