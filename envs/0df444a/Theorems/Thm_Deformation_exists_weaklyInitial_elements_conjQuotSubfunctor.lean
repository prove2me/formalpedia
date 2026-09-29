-- Prove2me | Theorems.Thm_Deformation_exists_weaklyInitial_elements_conjQuotSubfunctor
-- name    : Deformation.exists_weaklyInitial_elements_conjQuotSubfunctor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/a901db96-d7a3-53cb-9f36-1b68beb5a8ea
-- title:
--   Weak initiality descends to the conjugation quotient subfunctor
-- statement:
--   Fix a finite index type $n$ with decidable equality, a topological group $G$, and a commutative local ring $\mathcal{O}$; the relevant category is $\mathtt{ProartinianCat}\ \mathcal{O}$, whose objects are topological commutative $\mathcal{O}$-algebras that are local pro-Artinian over $\mathcal{O}$. Let $F$ be a subfunctor of [`Deformation.repnFunctor n G 𝓞`](def/Deformations_LiftFunctor.html#L18), the functor sending an object $R$ to the set of continuous monoid homomorphisms $G \to \mathrm{GL}_n(R)$, with functoriality by entrywise application of an algebra map. Let $T$ be an object of the category of elements of the functor underlying $F$, i.e. a pair consisting of an object $R$ and an element $\rho \in F(R)$, and assume $T$ is weakly initial: for every object $X$ of that category the set of morphisms $T \to X$ is nonempty. The conclusion asserts the existence of an object $T'$ of the category of elements of the functor underlying [`Deformation.conjQuotSubfunctor n F`](def/Deformations_ConjQuotSubfunctor.html#L22), the subfunctor of [`Deformation.repnQuotFunctor n G 𝓞`](def/Deformations_LiftFunctor.html#L39) whose value at $R$ is the image of $F(R)$ under the orbit map $\rho \mapsto [\rho]$ for conjugation by $\ker(\mathrm{GL}_n(R) \to \mathrm{GL}_n(k_R))$, such that for every object $X$ there the set of morphisms $T' \to X$ is nonempty.
--
--   This is the solution-set (weakly initial object) step for the unframed, conditioned deformation problem: a weakly initial object for a deformation condition $F$ on framed lifts produces one for the induced condition on lifts modulo strict equivalence. It is used by [`Deformation.isCorepresentable_conjQuotSubfunctor_of_descends`](thm.html#Deformation.isCorepresentable_conjQuotSubfunctor_of_descends) in the corepresentability argument for the quotient functor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Deformation_exists_weaklyInitial_elements_conjQuotSubfunctor.lean

import Mathlib
import Definitions.Def_Deformations_ConjQuotSubfunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory IsLocalRing

universe u v

theorem Deformation.exists_weaklyInitial_elements_conjQuotSubfunctor (n : Type) [Fintype n] [DecidableEq n] {G : Type u} [Group G]
  [TopologicalSpace G] {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞]
  {F : CategoryTheory.Subfunctor (Deformation.repnFunctor n G 𝓞)} (T : F.toFunctor.Elements)
  (hT : ∀ (X : F.toFunctor.Elements), Nonempty (T ⟶ X)) :
  ∃ T', ∀ (X : (Deformation.conjQuotSubfunctor n F).toFunctor.Elements), Nonempty (T' ⟶ X) := by sorry
