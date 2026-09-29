-- Prove2me | Theorems.Thm_CohCarrier_HeckeData_finite_opSubalgebra_and_subsingleton_ML_or_exists_corner
-- name    : CohCarrier.HeckeData.finite_opSubalgebra_and_subsingleton_ML_or_exists_corner
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/d8836c49-6e41-5717-b411-7cf7c0473cf7
-- title:
--   Finiteness of the Hecke operator algebra and corner alternative
-- statement:
--   Let $\mathcal{O}$ be a commutative Noetherian local ring which is adically complete for its maximal ideal, let $V$ be an $\mathcal{O}$-module that is module-finite over $\mathcal{O}$, and let $k$ be a field equipped with an $\mathcal{O}$-algebra structure for which `algebraMap 𝒪 k` is surjective. Let $D$ be a Hecke datum for these data, i.e. a type $D.\mathrm{Gen}$, a family $D.\mathrm{op} : D.\mathrm{Gen} \to \mathrm{End}_{\mathcal{O}}(V)$ of pairwise commuting $\mathcal{O}$-linear operators, and a function $D.\bar\theta : D.\mathrm{Gen} \to k$; throughout, $V$ carries the module structure over $D.\mathrm{FreeAlg} = \mathrm{MvPolynomial}\,(D.\mathrm{Gen})\,\mathcal{O}$ in which $X_g$ acts by $D.\mathrm{op}\,g$. Write $B = D.\mathrm{opSubalgebra} = \mathrm{Algebra.adjoin}_{\mathcal{O}}(\mathrm{range}\,D.\mathrm{op}) \subseteq \mathrm{End}_{\mathcal{O}}(V)$. The assertion is twofold: first, $B$ is module-finite over $\mathcal{O}$; second, either the $\mathcal{O}$-module `D.ML` attached to the datum is a subsingleton, or there are an idempotent splitting $S$ of $B$ — a natural number $S.n$, idempotents $S.e : \mathrm{Fin}\,S.n \to B$ forming a complete orthogonal family, and maximal ideals $S.\mathfrak{m}\,i$ of $B$ exhausting all maximal ideals, with $S.e\,i \in S.\mathfrak{m}\,j$ exactly when $i \neq j$ — an index $i$, and a surjective ring homomorphism $r$ from the corner ring $S.e\,i\,B\,S.e\,i$ to $k$ such that $r$ agrees with $\mathrm{algebraMap}$ on scalars from $\mathcal{O}$ and sends the corner image $S.e\,i \cdot D.\mathrm{op}\,g \cdot S.e\,i$ of each generator to $D.\bar\theta\,g$; moreover there is an $\mathcal{O}$-linear isomorphism $e$ from `D.ML` onto the corner submodule $S.e\,i \cdot V$ of $V$ carrying the action of $X_g$ to the action of that corner image of $D.\mathrm{op}\,g$.
--
--   This is the local structure theory of the Hecke algebra in the form used for Ihara-type arguments: a commutative algebra finite over a complete Noetherian local base splits by a complete family of orthogonal idempotents indexed by its maximal ideals, and the component cut out by a residual eigensystem $\bar\theta$ is realised concretely as a corner $e_i V$ of the carrier. It is invoked by the results that produce corner realisations for cohomology carriers at level $\Gamma_0$ and $\Gamma_H$ and in the level-raising refinement steps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_HeckeData_finite_opSubalgebra_and_subsingleton_ML_or_exists_corner.lean

import Definitions.Def_CohCarrier_HeckeData
import Definitions.Def_IharaLemma_IdempotentSplitting
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] CohCarrier.HeckeData.moduleFreeAlg
open scoped IsMulCommutative in

theorem CohCarrier.HeckeData.finite_opSubalgebra_and_subsingleton_ML_or_exists_corner
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module.Finite 𝒪 V]
    {k : Type} [Field k] [Algebra 𝒪 k] (hk : Function.Surjective (algebraMap 𝒪 k))
    (D : CohCarrier.HeckeData 𝒪 V k) :
    Module.Finite 𝒪 ↥D.opSubalgebra ∧
      (Subsingleton D.ML ∨
        ∃ (S : IharaLemma.IdempotentSplitting ↥D.opSubalgebra) (i : Fin S.n)
          (r : S.CornerRing i →+* k),
          Function.Surjective r ∧
            (∀ c : 𝒪, r (algebraMap 𝒪 (S.CornerRing i) c) = algebraMap 𝒪 k c) ∧
            (∀ g : D.Gen,
              r (S.toCornerRing i ⟨D.op g, Algebra.subset_adjoin (Set.mem_range_self g)⟩)
                = D.θbar g) ∧
            ∃ e : D.ML ≃ₗ[𝒪] ↥(IharaLemma.cornerSubmodule (M := V) (S.e i)),
              ∀ (g : D.Gen) (m : D.ML),
                e ((MvPolynomial.X g : D.FreeAlg) • m)
                  = S.toCornerRing i ⟨D.op g, Algebra.subset_adjoin (Set.mem_range_self g)⟩
                      • e m) := by sorry
