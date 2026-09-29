-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_isOpenImmersion_isClosedImmersion_iff_of_isIdempotentElem_of_forall_exists_idempotent_of_finiteType
-- name    : AlgebraicGeometry.Scheme.exists_isOpenImmersion_isClosedImmersion_iff_of_isIdempotentElem_of_forall_exists_idempotent_of_finiteType
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/d88d3ebe-c4b1-5f8f-b177-4a3b52a876bf
-- title:
--   Clopen subscheme representing a subfunctor cut out by idempotents
-- statement:
--   Let $R$ be a commutative ring and let $F$ assign to every commutative $R$-algebra $B$ a type $F\,B$, together with maps $\mathrm{Fmap}$ sending an $R$-algebra homomorphism $\varphi\colon B\to B'$ to a map $F\,B\to F\,B'$. Let $H$ be a scheme with a morphism $p_H\colon H\to\operatorname{Spec} R$ that is locally of finite type, and suppose given bijections $\mathrm{pt}_B\colon F\,B\;\simeq\;\{g\colon\operatorname{Spec} B\to H \mid g \text{ followed by } p_H \text{ equals } \operatorname{Spec}(\operatorname{algebraMap} R\,B)\}$, compatible with the maps $\mathrm{Fmap}$ in the sense that for every $R$-algebra map $\varphi\colon B\to B'$ and every $x\in F\,B$ the morphism underlying $\mathrm{pt}_{B'}(\mathrm{Fmap}\,\varphi\,x)$ is $\operatorname{Spec}\varphi$ followed by the morphism underlying $\mathrm{pt}_B(x)$. Let $P$ be a predicate on each $F\,B$ subject to the hypothesis that for every $R$-algebra $B$ of finite type and every $x\in F\,B$ there is an idempotent $e\in B$ with $P(\mathrm{Fmap}\,\varphi\,x)\iff\varphi(e)=1$ for all $R$-algebra maps $\varphi$ out of $B$. The conclusion asserts the existence of a scheme $X$ and a morphism $\iota\colon X\to H$ which is simultaneously an open immersion and a closed immersion, such that for every $R$-algebra $B$, every $x\in F\,B$ and every idempotent $e\in B$ satisfying that same witnessing condition for $x$, one has $P(x)$ if and only if the morphism underlying $\mathrm{pt}_B(x)$ factors as some $g\colon\operatorname{Spec} B\to X$ followed by $\iota$. Note that the characterisation of $P$ by factorisation through $\iota$ is asserted only at those points $x$ admitting a witnessing idempotent, not at arbitrary points of $F$.
--
--   This is the representability criterion for a subfunctor which is pointwise open-and-closed on finite-type points: such a subfunctor is cut out by a clopen subscheme, via the correspondence between idempotents of a ring and decompositions of its spectrum into open-and-closed pieces. It is used in the Cherednik–Drinfeld part of the construction, where the speciality locus inside a Hilbert-scheme-type moduli space is produced as a clopen subscheme and the criterion is applied at Noetherian, not necessarily finite-type, test algebras.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_exists_isOpenImmersion_isClosedImmersion_iff_of_isIdempotentElem_of_forall_exists_idempotent_of_finiteType.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.exists_isOpenImmersion_isClosedImmersion_iff_of_isIdempotentElem_of_forall_exists_idempotent_of_finiteType
    (R : Type) [CommRing R]
    (F : ∀ (B : Type) [CommRing B] [Algebra R B], Type)
    (Fmap : ∀ (B B' : Type) [CommRing B] [CommRing B'] [Algebra R B] [Algebra R B'], (B →ₐ[R] B') → F B → F B')
    (H : Scheme.{0}) (pH : H ⟶ Spec (CommRingCat.of R)) (hH : LocallyOfFiniteType pH)
    (pt : ∀ (B : Type) [CommRing B] [Algebra R B],
      F B ≃ {g : Spec (CommRingCat.of B) ⟶ H // g ≫ pH = Spec.map (CommRingCat.ofHom (algebraMap R B))})
    (hpt : ∀ (B B' : Type) [CommRing B] [CommRing B'] [Algebra R B] [Algebra R B'] (φ : B →ₐ[R] B') (x : F B),
      (pt B' (Fmap B B' φ x)).1 = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (pt B x).1)
    (P : ∀ (B : Type) [CommRing B] [Algebra R B], F B → Prop)
    (hP : ∀ (B : Type) [CommRing B] [Algebra R B] [Algebra.FiniteType R B] (x : F B), ∃ e : B, IsIdempotentElem e ∧
      ∀ (B' : Type) [CommRing B'] [Algebra R B'] (φ : B →ₐ[R] B'), P B' (Fmap B B' φ x) ↔ φ e = 1) :
    ∃ (X : Scheme.{0}) (ι : X ⟶ H), IsOpenImmersion ι ∧ IsClosedImmersion ι ∧
      ∀ (B : Type) [CommRing B] [Algebra R B] (x : F B) (e : B), IsIdempotentElem e →
        (∀ (B' : Type) [CommRing B'] [Algebra R B'] (φ : B →ₐ[R] B'), P B' (Fmap B B' φ x) ↔ φ e = 1) →
        (P B x ↔ ∃ g : Spec (CommRingCat.of B) ⟶ X, g ≫ ι = (pt B x).1) := by sorry
