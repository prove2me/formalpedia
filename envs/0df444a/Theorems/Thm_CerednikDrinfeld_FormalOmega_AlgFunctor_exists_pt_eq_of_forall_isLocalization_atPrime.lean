-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_AlgFunctor_exists_pt_eq_of_forall_isLocalization_atPrime
-- name    : CerednikDrinfeld.FormalOmega.AlgFunctor.exists_pt_eq_of_forall_isLocalization_atPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/0d8a8fd1-2121-5622-9e37-b720925d8e27
-- title:
--   Local-to-global for points of a scheme in a point functor
-- statement:
--   Let $C$ be a commutative ring and let $P$ be an `AlgFunctor C`, that is, an assignment of a type $P(B)$ to every commutative $C$-algebra $B$ together with maps $P(\varphi) : P(B) \to P(B')$ for $C$-algebra homomorphisms $\varphi$, compatible with identities and composition. Assume: (`hsep`) for every $C$-algebra $A$, every finite family $f_1,\dots,f_n \in A$ generating the unit ideal and every family of $C$-algebras $B_i$ that are localisations of $A$ away from $f_i$ (compatibly over $C$), two elements of $P(A)$ with the same image in each $P(B_i)$ are equal. Let $S$ be a Noetherian $C$-algebra and assume (`hlfp`) that for every $g \in S$, every Noetherian localisation $A$ of $S$ away from $g$, every prime $\mathfrak p \subset A$ and every localisation $L$ of $A$ at $\mathfrak p$, two elements of $P(A)$ with equal images in $P(L)$ already have equal images in $P(A_f)$ for some localisation of $A$ away from some $f \notin \mathfrak p$. Let $f_W : W \to \operatorname{Spec} C$ be a scheme locally of finite type, and write $(\mathrm{nilpPoints}\, f_W)(T)$ for the set of morphisms $\operatorname{Spec} T \to W$ over $\operatorname{Spec} C$. Let $\mathrm{pt}_T : (\mathrm{nilpPoints}\, f_W)(T) \to P(T)$ be maps, natural in $C$-algebra homomorphisms (`hnat`) and injective whenever $T$ is Noetherian (`hinj`). Then for $x \in P(S)$ such that for every prime $\mathfrak p$ of $S$ and every localisation $L$ of $S$ at $\mathfrak p$ the image of $x$ in $P(L)$ lies in the image of $\mathrm{pt}_L$, there exists $w \in (\mathrm{nilpPoints}\, f_W)(S)$ with $\mathrm{pt}_S(w) = x$.
--
--   A general spreading-out and gluing statement, with no Čerednik–Drinfeld content: a point of the functor $P$ over a Noetherian base $S$ that is representable by a $W$-point after localising at each prime is representable over $S$ itself. It is used in the Čerednik–Drinfeld uniformisation to globalise the edge-chart representability of rigidified pairs, in [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_represents_inEdgeChart_of_rigidifiedToG_of_bdd`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_represents_inEdgeChart_of_rigidifiedToG_of_bdd), and it relies on the gluing of sections over a finite cover by basic opens provided by [`AlgebraicGeometry.Scheme.section_ext_and_exists_section_of_isLocalizationAway_of_span_eq_top`](thm.html#AlgebraicGeometry.Scheme.section_ext_and_exists_section_of_isLocalizationAway_of_span_eq_top).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_AlgFunctor_exists_pt_eq_of_forall_isLocalization_atPrime.lean

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.AlgFunctor.exists_pt_eq_of_forall_isLocalization_atPrime
    {C : Type} [CommRing C] (P : AlgFunctor C)

    (hsep : ∀ (A : Type) [CommRing A] [Algebra C A] (n : ℕ) (f : Fin n → A), Ideal.span (Set.range f) = ⊤ →
      ∀ (B : Fin n → Type) [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)] [∀ i, Algebra C (B i)]
        [∀ i, IsScalarTower C A (B i)] [∀ i, IsLocalization.Away (f i) (B i)] (a b : P.obj A),
      (∀ i, P.map (IsScalarTower.toAlgHom C A (B i)) a = P.map (IsScalarTower.toAlgHom C A (B i)) b) → a = b)

    (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S]

    (hlfp : ∀ (g : S) (A : Type) [CommRing A] [Algebra S A] [Algebra C A] [IsScalarTower C S A] [IsLocalization.Away g A]
      [IsNoetherianRing A] (𝔭 : Ideal A) [𝔭.IsPrime]
      (L : Type) [CommRing L] [Algebra A L] [Algebra C L] [IsScalarTower C A L] [IsLocalization.AtPrime L 𝔭] (a b : P.obj A),
      P.map (IsScalarTower.toAlgHom C A L) a = P.map (IsScalarTower.toAlgHom C A L) b →
      ∃ (f : A) (_ : f ∉ 𝔭) (Af : Type) (_ : CommRing Af) (_ : Algebra A Af) (_ : Algebra C Af) (_ : IsScalarTower C A Af)
        (_ : IsLocalization.Away f Af),
        P.map (IsScalarTower.toAlgHom C A Af) a = P.map (IsScalarTower.toAlgHom C A Af) b)

    {W : Scheme.{0}} (fW : W ⟶ Spec (CommRingCat.of C)) (hW : LocallyOfFiniteType fW)
    (pt : ∀ (T : Type) [CommRing T] [Algebra C T], (Scheme.nilpPoints fW).obj T → P.obj T)
    (hnat : ∀ (T T' : Type) [CommRing T] [Algebra C T] [CommRing T'] [Algebra C T'] (φ : T →ₐ[C] T')
      (w : (Scheme.nilpPoints fW).obj T), pt T' ((Scheme.nilpPoints fW).map φ w) = P.map φ (pt T w))
    (hinj : ∀ (T : Type) [CommRing T] [Algebra C T] [IsNoetherianRing T]
      (w w' : (Scheme.nilpPoints fW).obj T), pt T w = pt T w' → w = w')

    (x : P.obj S)
    (hloc : ∀ (𝔭 : Ideal S) [𝔭.IsPrime] (L : Type) [CommRing L] [Algebra S L] [Algebra C L] [IsScalarTower C S L]
      [IsLocalization.AtPrime L 𝔭],
      ∃ w : (Scheme.nilpPoints fW).obj L, pt L w = P.map (IsScalarTower.toAlgHom C S L) x) :
    ∃ w : (Scheme.nilpPoints fW).obj S, pt S w = x := by sorry
