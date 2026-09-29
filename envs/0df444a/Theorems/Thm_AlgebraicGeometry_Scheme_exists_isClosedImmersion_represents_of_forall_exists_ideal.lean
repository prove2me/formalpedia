-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_isClosedImmersion_represents_of_forall_exists_ideal
-- name    : AlgebraicGeometry.Scheme.exists_isClosedImmersion_represents_of_forall_exists_ideal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/b3a4cce3-a1fc-50fb-815a-6b92511335f7
-- title:
--   Closed subfunctors of representable functors are represented by closed subschemes
-- statement:
--   Let $R$ be a commutative ring. Suppose given, for every commutative $R$-algebra $A$, a type $F\,A$, together with maps $F\,\varphi : F\,A \to F\,B$ assigned to $R$-algebra homomorphisms $\varphi : A \to B$ (no functoriality axioms are imposed on these assignments). Suppose given a scheme $X$ and a morphism $p : X \to \operatorname{Spec} R$, and for each $A$ a bijection $\mathrm{pt}_A$ from $F\,A$ onto the set of morphisms $g : \operatorname{Spec} A \to X$ with $g$ followed by $p$ equal to the structure morphism $\operatorname{Spec}(R \to A)$, these bijections being natural in the sense that for every $\varphi : A \to B$ and $s \in F\,A$ one has $\mathrm{pt}_B(F\,\varphi\,s) = \operatorname{Spec}\varphi$ followed by $\mathrm{pt}_A(s)$. Let $W\,A \subseteq F\,A$ be a predicate on each $F\,A$ satisfying the closedness hypothesis: for every $A$ and every $s \in F\,A$ there is an ideal $\mathfrak a \subseteq A$ such that for every commutative $R$-algebra $B$ and every $R$-algebra homomorphism $\varphi : A \to B$, the condition $W\,B$ holds of $F\,\varphi\,s$ if and only if $\varphi$ kills $\mathfrak a$. The conclusion asserts the existence of a scheme $Z$, a morphism $\iota : Z \to X$, and for each commutative $R$-algebra $A$ a bijection $\mathrm{pt}^Z_A$ from the subtype of $s \in F\,A$ with $W\,A\,s$ onto the set of morphisms $g : \operatorname{Spec} A \to Z$ with $g$ followed by $\iota$ followed by $p$ equal to $\operatorname{Spec}(R \to A)$, such that $\iota$ is a closed immersion and $\mathrm{pt}^Z_A(s)$ followed by $\iota$ equals $\mathrm{pt}_A(s)$ for all $A$ and all such $s$. All schemes here live in the zeroth universe, and representability is only asserted on affine test objects $\operatorname{Spec} A$.
--
--   This is the standard representability criterion for a closed subfunctor of a functor represented (on affine points) by a scheme: the pointwise ideals glue to a quasi-coherent ideal sheaf on $X$ whose zero scheme represents the subfunctor. It is used in the construction of Hilbert-type and Grassmannian-type parameter schemes as closed subschemes of ambient representing schemes, and in the treatment of polarised abelian schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_exists_isClosedImmersion_represents_of_forall_exists_ideal.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.exists_isClosedImmersion_represents_of_forall_exists_ideal
    (R : Type) [CommRing R]
    (F : ∀ (A : Type) [CommRing A] [Algebra R A], Type)
    (Fmap : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B],
      (A →ₐ[R] B) → F A → F B)
    (X : Scheme.{0}) (p : X ⟶ Spec (CommRingCat.of R))
    (pt : ∀ (A : Type) [CommRing A] [Algebra R A],
      F A ≃ {g : Spec (CommRingCat.of A) ⟶ X // g ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R A))})
    (pt_natural : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
      (φ : A →ₐ[R] B) (s : F A),
      (pt B (Fmap A B φ s)).1 = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (pt A s).1)
    (W : ∀ (A : Type) [CommRing A] [Algebra R A], F A → Prop)
    (closed : ∀ (A : Type) [CommRing A] [Algebra R A] (s : F A), ∃ 𝔞 : Ideal A,
      ∀ (B : Type) [CommRing B] [Algebra R B] (φ : A →ₐ[R] B),
        W B (Fmap A B φ s) ↔ ∀ a ∈ 𝔞, φ a = 0) :
    ∃ (Z : Scheme.{0}) (ι : Z ⟶ X)
      (ptZ : ∀ (A : Type) [CommRing A] [Algebra R A],
        {s : F A // W A s} ≃
          {g : Spec (CommRingCat.of A) ⟶ Z //
            g ≫ ι ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R A))}),
      IsClosedImmersion ι ∧
      ∀ (A : Type) [CommRing A] [Algebra R A] (s : {s : F A // W A s}),
        (ptZ A s).1 ≫ ι = (pt A s.1).1 := by sorry
