-- Prove2me | Theorems.Thm_AutomorphicForm_SplitPlace_mem_semiLocalIntegralSet_iff_coords_and_semiLocalWeight_eq_sum_and_map_coords_semiLocalHaar
-- name    : AutomorphicForm.SplitPlace.mem_semiLocalIntegralSet_iff_coords_and_semiLocalWeight_eq_sum_and_map_coords_semiLocalHaar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/e052f234-ffed-590a-8cda-15fabb31e18b
-- title:
--   Split-place coordinates: integrality, weights and Haar normalisation
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra whose degree $n=\operatorname{finrank}_K L$ is prime, let $\sigma$ be a $K$-algebra automorphism of $L$ with $\sigma\neq 1$, let $v$ be a height-one prime of $\mathcal{O}_K$ such that every height-one prime $w$ of $\mathcal{O}_L$ lying under which $v$ sits has ramification index $1$ over $v$, and let $\iota\colon L\to K_v$ be a $K$-algebra map into the $v$-adic completion. Write $\mathrm{coords}$ for the multiplicative isomorphism $GL_2(L\otimes_K K_v)\simeq (GL_2(K_v))^{\mathrm{Fin}(n-1+1)}$ obtained from [`AutomorphicForm.SplitPlace.psiGL`](def/AutomorphicForm_SplitFibreIntegral.html#L248) followed by the reindexing `reindex`, and equip both general linear groups with their Borel $\sigma$-algebras. Three assertions are made. First, for every $x$, the matrices of $x$ and $x^{-1}$ have all entries in the image of $\mathcal{O}_L\otimes\mathcal{O}_{K_v}$ in $L\otimes_K K_v$ if and only if, for each index $j$, the matrices of $\mathrm{coords}(x)_j$ and its inverse have all entries in $\mathcal{O}_{K_v}$. Second, the semi-local weight of $x$, the finite sum over the extensions of $v$ to $L$ of the local weights $2\log\bigl(\max(\|g_{00}\|,\|g_{01}\|)\cdot\mathrm{rowMaxNorm}(g)/\|\det g\|\bigr)$ of its place components, equals $\sum_j$ of the local weights of $\mathrm{coords}(x)_j$. Third, $\mathrm{coords}$ pushes the Haar measure on $GL_2(L\otimes_K K_v)$ normalised by the semi-local integral set forward to the product of the copies of the Haar measure on $GL_2(K_v)$ normalised by the local integral set.
--
--   This is the split-place compatibility of the coordinate isomorphism at an unramified prime: the three structures entering twisted weighted orbital integrals — integral points, adelic height weights and the unit-normalised Haar measures — all decompose along the $n$ factors. It is used in the proof of [`AutomorphicForm.twistedWeighted_eq_finrank_mul_weighted_heckeWord_of_inertiaDeg_eq_one`](thm.html#AutomorphicForm.twistedWeighted_eq_finrank_mul_weighted_heckeWord_of_inertiaDeg_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_SplitPlace_mem_semiLocalIntegralSet_iff_coords_and_semiLocalWeight_eq_sum_and_map_coords_semiLocalHaar.lean

import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_SplitFibreIntegral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.SplitPlace.mem_semiLocalIntegralSet_iff_coords_and_semiLocalWeight_eq_sum_and_map_coords_semiLocalHaar
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hprime : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (ι : L →ₐ[K] v.adicCompletion K) :
    letI : FiniteDimensional K L := Module.finite_of_finrank_pos hprime.pos
    letI : MeasurableSpace (GL (Fin 2) (v.adicCompletion K)) := AutomorphicForm.localGLBorel K v
    letI : MeasurableSpace (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
    (∀ x : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
        x ∈ AutomorphicForm.semiLocalIntegralSet K L v ↔
          ∀ j, AutomorphicForm.SplitPlace.coords (v.adicCompletion K) σ ι hprime hσ x j ∈ AutomorphicForm.localIntegralSet K v) ∧
    (∀ x : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
        AutomorphicForm.semiLocalWeight K L v x =
          ∑ j, AutomorphicForm.LocalWeight.weight (AutomorphicForm.SplitPlace.coords (v.adicCompletion K) σ ι hprime hσ x j)) ∧
    Measure.map (AutomorphicForm.SplitPlace.coords (v.adicCompletion K) σ ι hprime hσ) (AutomorphicForm.semiLocalHaar K L v) =
      Measure.pi (fun _ => AutomorphicForm.localHaar K v) := by sorry
