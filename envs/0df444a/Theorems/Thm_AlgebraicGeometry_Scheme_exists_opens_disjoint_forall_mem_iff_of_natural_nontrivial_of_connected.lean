-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_opens_disjoint_forall_mem_iff_of_natural_nontrivial_of_connected
-- name    : AlgebraicGeometry.Scheme.exists_opens_disjoint_forall_mem_iff_of_natural_nontrivial_of_connected
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/cad2b190-521b-5327-a729-99721ff45331
-- title:
--   Natural finite labellings of points come from open decompositions
-- statement:
--   Let $C$ be a Noetherian commutative ring, let $X$ be a scheme (in the bottom universe) and let $fX : X \to \operatorname{Spec} C$ be a morphism that is locally of finite type, and let $L$ be a finite type with decidable equality. For a commutative $C$-algebra $S$, write $X(S)$ for the set of morphisms $\varphi : \operatorname{Spec} S \to X$ with $\varphi$ followed by $fX$ equal to $\operatorname{Spec}$ of the structure map $C \to S$; a $C$-algebra map $g : S \to S'$ acts by sending $\varphi$ to $\operatorname{Spec}(g)$ followed by $\varphi$ (this is the functor `Scheme.nilpPoints fX`). Assume given, for every Noetherian $C$-algebra $S$ all of whose idempotents are $0$ or $1$, a labelling map $\mathrm{lab}_S : X(S) \to L$, and assume naturality in the following restricted form: for all such $S$, $S'$ with $S'$ in addition nontrivial, every $C$-algebra map $g : S \to S'$ and every $x \in X(S)$, the label of the image of $x$ in $X(S')$ equals the label of $x$. Then there is a family of opens $U : L \to X.\mathrm{Opens}$ which is pairwise disjoint ($U_l \cap U_{l'} = \emptyset$ for $l \neq l'$), whose supremum is all of $X$, and which computes the labelling: for every nontrivial Noetherian $C$-algebra $S$ with only the idempotents $0, 1$, every $x \in X(S)$ and every $l \in L$, one has $\mathrm{lab}_S(x) = l$ if and only if the underlying continuous map of $x$ carries every point of $\operatorname{Spec} S$ into $U_l$.
--
--   This is the representability step converting a functorially defined finite invariant of points of $X$ over Noetherian connected (in the sense of having no nontrivial idempotents) $C$-algebras into a decomposition of $X$ into finitely many pairwise disjoint opens, indexed by the label set, the label being read off as the unique piece containing the image of a point. It is used in the Čerednik–Drinfeld chapter, where the labelling of points by pieces of the Bruhat–Tits tree is shown to be injective and surjective on the relevant charts.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_exists_opens_disjoint_forall_mem_iff_of_natural_nontrivial_of_connected.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.exists_opens_disjoint_forall_mem_iff_of_natural_nontrivial_of_connected
    {C : Type} [CommRing C] [IsNoetherianRing C] (X : Scheme.{0}) (fX : X ⟶ Spec (CommRingCat.of C)) [LocallyOfFiniteType fX]
    (L : Type) [Fintype L] [DecidableEq L]
    (lab : ∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S],
      (∀ e : S, IsIdempotentElem e → e = 0 ∨ e = 1) → (Scheme.nilpPoints fX).obj S → L)
    (hnat : ∀ (S S' : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [CommRing S'] [Algebra C S'] [IsNoetherianRing S'] [Nontrivial S']
      (hS : (∀ e : S, IsIdempotentElem e → e = 0 ∨ e = 1)) (hS' : (∀ e : S', IsIdempotentElem e → e = 0 ∨ e = 1))
      (g : S →ₐ[C] S') (x : (Scheme.nilpPoints fX).obj S),
      lab S' hS' ((Scheme.nilpPoints fX).map g x) = lab S hS x) :
    ∃ U : L → X.Opens,
      (∀ l l' : L, l ≠ l' → Disjoint (U l) (U l')) ∧ (⨆ l, U l) = ⊤ ∧
      ∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Nontrivial S] (hS : (∀ e : S, IsIdempotentElem e → e = 0 ∨ e = 1))
        (x : (Scheme.nilpPoints fX).obj S) (l : L),
        lab S hS x = l ↔ ∀ p : ↥(Spec (CommRingCat.of S)), x.1.base p ∈ U l := by sorry
