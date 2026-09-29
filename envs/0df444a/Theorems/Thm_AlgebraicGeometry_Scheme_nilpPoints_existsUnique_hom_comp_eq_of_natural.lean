-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_nilpPoints_existsUnique_hom_comp_eq_of_natural
-- name    : AlgebraicGeometry.Scheme.nilpPoints.existsUnique_hom_comp_eq_of_natural
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/80c67bb5-0d25-5ebe-bcdf-6fe62fc8bcca
-- title:
--   Unique morphism induced by natural maps on nilpotent points
-- statement:
--   Let $\mathcal O$ be a commutative ring, $\pi \in \mathcal O$, and let $f : X \to \operatorname{Spec}\mathcal O$ and $t : T \to \operatorname{Spec}\mathcal O$ be morphisms of schemes. For a commutative $\mathcal O$-algebra $B$ write $X(B)$ for the set of morphisms $\varphi : \operatorname{Spec} B \to X$ with $\varphi$ followed by $f$ equal to $\operatorname{Spec}$ of the structure map $\mathcal O \to B$, an $\mathcal O$-algebra map $g : B \to B'$ acting by $\varphi \mapsto \varphi \circ \operatorname{Spec} g$, and similarly for $T$. Assume given maps $u_B : X(B) \to T(B)$ for every $\mathcal O$-algebra $B$ in which the image of $\pi$ is nilpotent, compatible with every $\mathcal O$-algebra homomorphism between two such algebras. Let $a : X' \to X$ be a morphism, $n \in \mathbb N$, and suppose $a$ followed by $f$ factors, via a morphism $b : X' \to \operatorname{Spec}(\mathcal O/(\pi^{n+1}))$, through $\operatorname{Spec}$ of the quotient map $\mathcal O \to \mathcal O/(\pi^{n+1})$. Then there is a unique morphism $s : X' \to T$ such that $s$ followed by $t$ equals $a$ followed by $f$, and such that for every $\mathcal O$-algebra $B$ in which $\pi$ is nilpotent and every $p : \operatorname{Spec} B \to X'$ with $p$ followed by $a$ followed by $f$ equal to $\operatorname{Spec}$ of $\mathcal O \to B$, the composite $p$ followed by $s$ is the morphism underlying $u_B(p \circ a)$.
--
--   This is the functor-of-points gluing step: a natural transformation defined only on points with values in $\mathcal O$-algebras where $\pi$ is nilpotent determines a genuine morphism of schemes out of any $X'$ whose structure morphism is killed by a power of $\pi$. It is used in the Čerednik–Drinfeld part of the development, where it feeds the identification of a formal quotient datum with the Čerednik–Drinfeld quotient.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_nilpPoints_existsUnique_hom_comp_eq_of_natural.lean

import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry CerednikDrinfeld.FormalOmega

theorem AlgebraicGeometry.Scheme.nilpPoints.existsUnique_hom_comp_eq_of_natural
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪)
    (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of 𝒪)) (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of 𝒪))
    (u : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
      (Scheme.nilpPoints f).obj B → (Scheme.nilpPoints t).obj B)
    (hu : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
      (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (y : (Scheme.nilpPoints f).obj B),
      u B' hB' ((Scheme.nilpPoints f).map φ y) = (Scheme.nilpPoints t).map φ (u B hB y))

    (X' : Scheme.{0}) (a : X' ⟶ X) (n : ℕ) (b : X' ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))
    (hb : b ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))) = a ≫ f) :
    ∃! s : X' ⟶ T, s ≫ t = a ≫ f ∧
      ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (p : Spec (CommRingCat.of B) ⟶ X')
        (hp : p ≫ a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap 𝒪 B))),
        p ≫ s = (u B hB ⟨p ≫ a, hp⟩).1 := by sorry
