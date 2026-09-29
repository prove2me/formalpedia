-- Prove2me | Theorems.Thm_CerednikDrinfeld_exists_torsionFree_surjective_comp_eq
-- name    : CerednikDrinfeld.exists_torsionFree_surjective_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/e4d2f086-19e4-5168-90ee-a28ed2390b12
-- title:
--   Factoring a ring map through a p-torsion-free surjection
-- statement:
--   Let $p$ be a natural number (no primality is assumed), let $S$ and $B$ be commutative rings, and let $h \colon S \to B$ be a ring homomorphism. Assume $S$ is $p$-torsion-free in the sense that for every $s \in S$, $(p \cdot 1_S)\, s = 0$ implies $s = 0$. The assertion is that there exist a type $T$ carrying a commutative ring structure together with ring homomorphisms $i \colon S \to T$ and $q \colon T \to B$ such that: $T$ is $p$-torsion-free in the same sense (for every $t \in T$, $(p \cdot 1_T)\, t = 0$ implies $t = 0$); $q$ is surjective as a function; and $q \circ i = h$ as ring homomorphisms $S \to B$. Thus any ring map out of a $p$-torsion-free ring can be factored through a $p$-torsion-free ring that maps onto the target, at the cost of enlarging the source.
--
--   This is a bookkeeping step used to replace a target ring by a $p$-torsion-free ring surjecting onto it, so that constructions may be carried out on $p$-torsion-free rings and then pushed forward. It is cited in the treatment of canonical $L$-maps for graded Cartier module data, in the lemmas [`CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.comp_eq_nMap_comp_of_isNilpotent`](thm.html#CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.comp_eq_nMap_comp_of_isNilpotent) and [`CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.exists_of_isBaseChangeAlong`](thm.html#CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.exists_of_isBaseChangeAlong).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_exists_torsionFree_surjective_comp_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CerednikDrinfeld.exists_torsionFree_surjective_comp_eq
    (p : ℕ) {S B : Type} [CommRing S] [CommRing B] (h : S →+* B) (hS : ∀ s : S, (p : S) * s = 0 → s = 0) :
    ∃ (T : Type) (_ : CommRing T) (i : S →+* T) (q : T →+* B),
      (∀ t : T, (p : T) * t = 0 → t = 0) ∧ Function.Surjective q ∧ q.comp i = h := by sorry
