-- Prove2me | Theorems.Thm_AutomorphicForm_exists_contDiff_hasCompactSupport_forall_apply_norm_eq_integral_ker_norm_prod_of_contDiff
-- name    : AutomorphicForm.exists_contDiff_hasCompactSupport_forall_apply_norm_eq_integral_ker_norm_prod_of_contDiff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/5108e9d1-1a94-5f4e-9510-bcbc9191b96c
-- title:
--   Norm-fibre integral of an archimedean test function is smooth
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a finite Galois extension of $K$, write $K_\infty$ for `InfiniteAdeleRing K` and $E = L \otimes_K K_\infty$, and equip the unit group $E^\times$ with a measurable structure that is the Borel structure of its topology. Let $N$ denote the map on units induced by the algebra norm $\mathrm{Algebra.norm}$ of $E$ over $K_\infty$, let $\theta$ be a Haar measure on $\ker N \le E^\times$, and write $\iota_L$ for the composite of [`AutomorphicForm.archIdent K L`](def/AutomorphicForm_TwistedOrbital.html#L420) (the commutativity isomorphism $L \otimes_K K_\infty \cong K_\infty \otimes_K L$ followed by the base-change ring isomorphism onto `InfiniteAdeleRing L` attached to `genuineInfinitePlaceData`) with the isomorphism `ringEquiv_mixedSpace L` onto the mixed space of $L$, and $\iota_K$ for `ringEquiv_mixedSpace K`. Let $G \colon (\mathrm{Fin}\,2 \to \mathrm{mixedSpace}\,L) \to \mathbb{C}$ be $C^\infty$ over $\mathbb{R}$ with compact support, and assume there is a compact set $C \subseteq E^\times \times E^\times$ such that every $p$ in the topological support of $G$ has $p\,0 = \iota_L(q_1)$ and $p\,1 = \iota_L(q_2)$ for some $(q_1,q_2) \in C$. Then there exists $F \colon (\mathrm{Fin}\,2 \to \mathrm{mixedSpace}\,K) \to \mathbb{C}$ that is $C^\infty$ over $\mathbb{R}$, has compact support, admits a compact $C_a \subseteq K_\infty^\times \times K_\infty^\times$ such that every point of the topological support of $F$ is the vector $![\iota_K(q_1), \iota_K(q_2)]$ for some $(q_1,q_2) \in C_a$, and is such that for all $\alpha, \beta \in E^\times$ the function $(u_1,u_2) \mapsto G\,![\iota_L(\alpha u_1), \iota_L(\beta u_2)]$ on $\ker N \times \ker N$ is integrable for $\theta \times \theta$ and $$F\,![\iota_K(N\alpha), \iota_K(N\beta)] = \int_{\ker N \times \ker N} G\,![\iota_L(\alpha u_1), \iota_L(\beta u_2)]\, \mathrm{d}(\theta \times \theta).$$
--
--   This is the fibre-integration step for archimedean twisted orbital integrals: since the fibres of the norm map are cosets of $\ker N$ and $\theta$ is invariant, integrating a smooth compactly supported test function over the norm-one fibre produces a smooth compactly supported function of the pair of norms, again carried over a compact set of unit pairs. It feeds the per-place archimedean computations at real and complex places used in the Langlands–Tunnell base-change argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_contDiff_hasCompactSupport_forall_apply_norm_eq_integral_ker_norm_prod_of_contDiff.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_FactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

attribute [local instance] AutomorphicForm.centralizerBorel AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)
open scoped ENNReal Classical

theorem AutomorphicForm.exists_contDiff_hasCompactSupport_forall_apply_norm_eq_integral_ker_norm_prod_of_contDiff
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)ˣ] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)ˣ]
    (θ : Measure ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) [θ.IsHaarMeasure]
    (G : (Fin 2 → NumberField.mixedEmbedding.mixedSpace L) → ℂ) (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (hGc : HasCompactSupport G)
    (hGu : ∃ C : Set ((L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ), IsCompact C ∧
        ∀ p ∈ tsupport G, ∃ q ∈ C,
          p 0 = NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((q.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))) ∧
          p 1 = NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((q.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)))) :
    ∃ F : (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) F ∧ HasCompactSupport F ∧
      (∃ Ca : Set ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ), IsCompact Ca ∧
        ∀ p ∈ tsupport F, ∃ q ∈ Ca,
          p = ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K),
                NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.2 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)]) ∧
      ∀ α β : (L ⊗[K] InfiniteAdeleRing K)ˣ,
        Integrable (fun u : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker =>
          G ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)))]) (θ.prod θ) ∧
        F ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (Algebra.norm (InfiniteAdeleRing K) ((α : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))),
            NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (Algebra.norm (InfiniteAdeleRing K) ((β : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)))] =
          ∫ u : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker,
            G ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)))] ∂(θ.prod θ) := by sorry
