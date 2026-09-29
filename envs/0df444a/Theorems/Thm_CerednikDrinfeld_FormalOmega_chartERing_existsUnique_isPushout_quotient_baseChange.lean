-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_chartERing_existsUnique_isPushout_quotient_baseChange
-- name    : CerednikDrinfeld.FormalOmega.chartERing.existsUnique_isPushout_quotient_baseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/a0e617cf-4066-527c-9312-e61860e1f2f8
-- title:
--   Truncated edge chart rings commute with base change
-- statement:
--   Let $R$ be a commutative ring, $\pi \in R$, and $q, n$ natural numbers, and let $S$ be a commutative $R$-algebra. Write $A(R) :=$ `chartERing R π q` for the localisation of $\mathrm{MvPolynomial}(\mathrm{Fin}\,2, R)/(\mathtt{edgeRel}\,R\,\pi)$ away from the image $\mathtt{edgeQuot.discr}\,R\,\pi\,q$ of $\mathtt{edgeDiscr}\,R\,q$, and $A(S) :=$ `chartERing S (algebraMap R S π) q` for the same construction over $S$ with $\pi$ replaced by its image. The assertion is that there is a ring homomorphism $\varphi$ from $A(R)/(\pi_{A(R)}^{\,n+1})$ to $A(S)/(\pi_{A(S)}^{\,n+1})$, where $\pi_{A(R)}$, $\pi_{A(S)}$ denote the images of $\pi$ under the respective structure maps, such that: the square formed by the induced quotient maps $R/(\pi^{n+1}) \to S/(\pi^{n+1})$, $R/(\pi^{n+1}) \to A(R)/(\pi_{A(R)}^{\,n+1})$, $S/(\pi^{n+1}) \to A(S)/(\pi_{A(S)}^{\,n+1})$ and $\varphi$ commutes; $\varphi$ carries the class of $\mathtt{chartERing.ξ}\,R\,\pi\,q$ to the class of $\mathtt{chartERing.ξ}\,S\,(\pi)\,q$ and likewise for the elements $\eta$; this square is a pushout in `CommRingCat`, with $A(S)/(\pi_{A(S)}^{\,n+1})$ as pushout object; and $\varphi$ is the unique ring homomorphism satisfying the three displayed compatibilities.
--
--   This is the base-change compatibility of the $(n+1)$-st truncations of the edge chart rings: $A(S)/\pi^{n+1} \cong (A(R)/\pi^{n+1}) \otimes_{R/\pi^{n+1}} S/\pi^{n+1}$, in the charts used for the formal model of the $p$-adic upper half plane. It is used in the construction of presentations for the Mumford tower, being cited by [`CerednikDrinfeld.FormalOmega.MumfordTower.nonempty_nrPresentation`](thm.html#CerednikDrinfeld.FormalOmega.MumfordTower.nonempty_nrPresentation).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_chartERing_existsUnique_isPushout_quotient_baseChange.lean

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.chartERing.existsUnique_isPushout_quotient_baseChange
    (R : Type) [CommRing R] (π : R) (q n : ℕ) (S : Type) [CommRing S] [Algebra R S] :
    ∃ φ : (chartERing R π q ⧸ Ideal.span {(algebraMap R (chartERing R π q) π) ^ (n + 1)}) →+*
        (chartERing S (algebraMap R S π) q ⧸ Ideal.span {(algebraMap S (chartERing S (algebraMap R S π) q) (algebraMap R S π)) ^ (n + 1)}),
      φ.comp (Ideal.quotientMap (Ideal.span {(algebraMap R (chartERing R π q) π) ^ (n + 1)}) (algebraMap R (chartERing R π q))
          (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl) :
            R ⧸ Ideal.span {π ^ (n + 1)} →+* _) =
        (Ideal.quotientMap (Ideal.span {(algebraMap S (chartERing S (algebraMap R S π) q) (algebraMap R S π)) ^ (n + 1)})
            (algebraMap S (chartERing S (algebraMap R S π) q))
            (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl) :
              S ⧸ Ideal.span {(algebraMap R S π) ^ (n + 1)} →+* _).comp
          (Ideal.quotientMap (Ideal.span {(algebraMap R S π) ^ (n + 1)}) (algebraMap R S)
            (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl)) ∧
      φ (Ideal.Quotient.mk _ (chartERing.ξ R π q)) = Ideal.Quotient.mk _ (chartERing.ξ S (algebraMap R S π) q) ∧
      φ (Ideal.Quotient.mk _ (chartERing.η R π q)) = Ideal.Quotient.mk _ (chartERing.η S (algebraMap R S π) q) ∧
      IsPushout
        (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap R S π) ^ (n + 1)}) (algebraMap R S)
          (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl) :
            R ⧸ Ideal.span {π ^ (n + 1)} →+* S ⧸ Ideal.span {(algebraMap R S π) ^ (n + 1)}))
        (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap R (chartERing R π q) π) ^ (n + 1)}) (algebraMap R (chartERing R π q))
          (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl) :
            R ⧸ Ideal.span {π ^ (n + 1)} →+* _))
        (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap S (chartERing S (algebraMap R S π) q) (algebraMap R S π)) ^ (n + 1)})
            (algebraMap S (chartERing S (algebraMap R S π) q))
            (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl) :
              S ⧸ Ideal.span {(algebraMap R S π) ^ (n + 1)} →+* _))
        (CommRingCat.ofHom φ) ∧
      ∀ φ' : (chartERing R π q ⧸ Ideal.span {(algebraMap R (chartERing R π q) π) ^ (n + 1)}) →+*
          (chartERing S (algebraMap R S π) q ⧸ Ideal.span {(algebraMap S (chartERing S (algebraMap R S π) q) (algebraMap R S π)) ^ (n + 1)}),
        φ'.comp (Ideal.quotientMap (Ideal.span {(algebraMap R (chartERing R π q) π) ^ (n + 1)}) (algebraMap R (chartERing R π q))
            (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl) :
              R ⧸ Ideal.span {π ^ (n + 1)} →+* _) =
          (Ideal.quotientMap (Ideal.span {(algebraMap S (chartERing S (algebraMap R S π) q) (algebraMap R S π)) ^ (n + 1)})
              (algebraMap S (chartERing S (algebraMap R S π) q))
              (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl) :
                S ⧸ Ideal.span {(algebraMap R S π) ^ (n + 1)} →+* _).comp
            (Ideal.quotientMap (Ideal.span {(algebraMap R S π) ^ (n + 1)}) (algebraMap R S)
              (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl)) →
        φ' (Ideal.Quotient.mk _ (chartERing.ξ R π q)) = Ideal.Quotient.mk _ (chartERing.ξ S (algebraMap R S π) q) →
        φ' (Ideal.Quotient.mk _ (chartERing.η R π q)) = Ideal.Quotient.mk _ (chartERing.η S (algebraMap R S π) q) → φ' = φ := by sorry
