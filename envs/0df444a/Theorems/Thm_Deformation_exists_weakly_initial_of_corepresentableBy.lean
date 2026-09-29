-- Prove2me | Theorems.Thm_Deformation_exists_weakly_initial_of_corepresentableBy
-- name    : Deformation.exists_weakly_initial_of_corepresentableBy
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/cee1689a-2910-5ca9-8ce1-130bbc2c102c
-- title:
--   Corepresentable subfunctors have a weakly initial element
-- statement:
--   Fix a finite index type $n$, a topological group $G$ and a commutative local ring $\mathcal{O}$ (with $G$ and $\mathcal{O}$ in the same universe). Let $\mathrm{Deformation.repnFunctor}\,n\,G\,\mathcal{O}$ be the covariant functor on [`Deformation.ProartinianCat 𝓞`](def/Deformations_ProartinianCat.html#L44) — the category whose objects are topological $\mathcal{O}$-algebras $A$ that are local, pro-Artinian, with $\mathcal{O} \to A$ a local homomorphism inducing an isomorphism on residue fields — sending $A$ to the set of continuous monoid homomorphisms $G \to \mathrm{GL}_n(A)$, a morphism $f \colon A \to B$ acting by post-composition with the map $\mathrm{GL}_n(A) \to \mathrm{GL}_n(B)$ obtained from $f$ applied entrywise to matrices. Let $F$ be a subfunctor of this functor, and let $R$ be an object of [`Deformation.ProartinianCat 𝓞`](def/Deformations_ProartinianCat.html#L44) together with a datum $e$ exhibiting $F$ as corepresented by $R$, i.e. a natural bijection between $\mathrm{Hom}(R, -)$ and $F$. The conclusion is that the category of elements of $F$ has a weakly initial object: there exists an element $T$, that is a pair consisting of an object $A$ and a point of $F(A)$, such that for every element $X$ the set of morphisms $T \to X$ in the category of elements is nonempty.
--
--   This is the passage from framed pro-representability of a deformation condition to the weaker, purely existential hypothesis (existence of a weakly initial element of the category of elements) used by the conditioned corepresentability machinery; only the existence of some morphism, not its uniqueness, is recorded. It is cited in the construction of the deformation ring data for a Galois representation, [`GaloisRep.nonempty_deformationRingData`](thm.html#GaloisRep.nonempty_deformationRingData).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Deformation_exists_weakly_initial_of_corepresentableBy.lean

import Mathlib
import Definitions.Def_Deformations_LiftFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory

universe u

theorem Deformation.exists_weakly_initial_of_corepresentableBy
    {n : Type} [Fintype n] [DecidableEq n] {G : Type u} [Group G] [TopologicalSpace G]
    {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞]
    {F : Subfunctor (Deformation.repnFunctor n G 𝓞)} {R : Deformation.ProartinianCat 𝓞}
    (e : F.toFunctor.CorepresentableBy R) :
    ∃ T : F.toFunctor.Elements, ∀ X : F.toFunctor.Elements, Nonempty (T ⟶ X) := by sorry
