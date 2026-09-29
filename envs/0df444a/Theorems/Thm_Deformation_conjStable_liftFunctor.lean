-- Prove2me | Theorems.Thm_Deformation_conjStable_liftFunctor
-- name    : Deformation.conjStable_liftFunctor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/a2f67883-0d2a-54f7-b3c4-19aaa38ab7eb
-- title:
--   Conjugation stability of the lift subfunctor
-- statement:
--   Let $\mathcal{O}$ be a commutative local ring, $n$ a finite index type with decidable equality, and $G$ a group carrying a topology. Let $\mathcal{C}_{\mathcal{O}} =$ `ProartinianCat 𝓞` be the category whose objects are topological $\mathcal{O}$-algebras that are local, pro-Artinian, topological rings, with $\mathcal{O} \to A$ a local homomorphism inducing a surjection onto the residue field of $A$; `repnFunctor n G 𝓞` sends $A$ to the set of continuous monoid homomorphisms $G \to \mathrm{GL}_n(A)$ and a morphism $f$ to pushforward of a representation along the entrywise map $\mathrm{GL}_n(A) \to \mathrm{GL}_n(B)$. Fix $\rho_0 : G \to \mathrm{GL}_n(k)$ continuous, where $k$ is the residue field of $\mathcal{O}$, viewed with the discrete topology as the terminal object of $\mathcal{C}_{\mathcal{O}}$. Then the subfunctor `liftFunctor n G 𝓞 ρ₀`, whose value at $A$ is the set of continuous $\rho'$ whose pushforward along the unique morphism $A \to k$ equals $\rho_0$, satisfies `ConjStable`: for every object $A$, every $\rho'$ in that set, and every $\gamma \in \mathrm{ConjAct}(\mathrm{GL}_n(A))$ whose underlying matrix lies in the kernel of $\mathrm{GL}_n(A) \to \mathrm{GL}_n(A/\mathfrak{m}_A)$, the conjugate $\gamma \cdot \rho'$ again lies in that set.
--
--   This is the conjugation-stability axiom for deformation conditions, verified for the unconditional framed lift functor $D^{\square}_{\bar\rho}$: strict equivalence, i.e. conjugation by matrices congruent to the identity modulo the maximal ideal, preserves the property of being a lift of $\bar\rho$. It is the fact that makes strict equivalence an equivalence relation on lifts, and it is used in the verification of the same axiom for conditioned subfunctors of Galois representations ([`GaloisRep.conjStable_conditionSubfunctor`](thm.html#GaloisRep.conjStable_conditionSubfunctor)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Deformation_conjStable_liftFunctor.lean

import Mathlib
import Definitions.Def_Deformations_ConjQuotSubfunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory IsLocalRing

universe u v

theorem Deformation.conjStable_liftFunctor {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞] {n : Type} [Fintype n] [DecidableEq n]
  {G : Type u} [Group G] [TopologicalSpace G]
  (ρ₀ : (Deformation.repnFunctor n G 𝓞).obj Deformation.ProartinianCat.residueField) :
  Deformation.ConjStable n (Deformation.liftFunctor n G 𝓞 ρ₀) := by sorry
