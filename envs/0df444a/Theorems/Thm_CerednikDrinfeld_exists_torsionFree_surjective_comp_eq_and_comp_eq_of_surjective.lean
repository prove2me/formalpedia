-- Prove2me | Theorems.Thm_CerednikDrinfeld_exists_torsionFree_surjective_comp_eq_and_comp_eq_of_surjective
-- name    : CerednikDrinfeld.exists_torsionFree_surjective_comp_eq_and_comp_eq_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/403956b1-ab7a-5cca-939d-107e552f1a24
-- title:
--   Lifting a ℤ_{p²}-structure along a p-torsion-free surjection
-- statement:
--   Let $p$ be a prime and write $\mathbb{Z}_{p^2}$ for [`CerednikDrinfeld.Zp2 p`](def/CerednikDrinfeld_SpecialFormalModule.html#L17), the ring $W(\mathbb{F}_{p^2})$ of Witt vectors of the Galois field with $p^2$ elements. Let $S$ and $B$ be commutative rings (in `Type`), let $\varphi\colon S \to B$ be a surjective ring homomorphism, assume $S$ is $p$-torsion-free in the sense that $p\cdot s = 0$ implies $s = 0$ for all $s \in S$, and let $j\colon \mathbb{Z}_{p^2} \to B$ be a ring homomorphism. Then there exist a commutative ring $S'$ (again in `Type`) and ring homomorphisms $\iota\colon S \to S'$, $j'\colon \mathbb{Z}_{p^2} \to S'$ and $q\colon S' \to B$ such that $S'$ is $p$-torsion-free in the same sense, $q$ is surjective, and $q \circ \iota = \varphi$ together with $q \circ j' = j$. No compatibility between $\iota$ and $j'$ beyond these two factorisations is asserted.
--
--   The statement normalises a $p$-torsion-free surjective lift $S \twoheadrightarrow B$ so that a prescribed $\mathbb{Z}_{p^2}$-structure on $B$ is itself lifted, which is the hypothesis under which two such lifts can be compared in the Cartier-theoretic treatment of special formal $\mathcal{O}_D$-modules. It is used in the proofs that the canonical map attached to graded Cartier module data is compatible with composition over $p$-torsion-free bases ([`CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.apply_comp_eq_nMap_apply_of_torsionFree`](thm.html#CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.apply_comp_eq_nMap_apply_of_torsionFree)) and that it is determined in the nilpotent case (`…IsCanonicalLMap.eq_of_isNilpotent`).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_exists_torsionFree_surjective_comp_eq_and_comp_eq_of_surjective.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CerednikDrinfeld.exists_torsionFree_surjective_comp_eq_and_comp_eq_of_surjective
    (p : ℕ) [Fact p.Prime] {S B : Type} [CommRing S] [CommRing B]
    (φ : S →+* B) (hφ : Function.Surjective φ) (hS : ∀ s : S, (p : S) * s = 0 → s = 0)
    (j : CerednikDrinfeld.Zp2 p →+* B) :
    ∃ (S' : Type) (_ : CommRing S') (ι : S →+* S') (j' : CerednikDrinfeld.Zp2 p →+* S') (q : S' →+* B),
      (∀ s : S', (p : S') * s = 0 → s = 0) ∧ Function.Surjective q ∧ q.comp ι = φ ∧ q.comp j' = j := by sorry
