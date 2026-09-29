-- Prove2me | Theorems.Thm_AutomorphicForm_isHaarMeasure_map_and_exists_isHaarMeasure_centralizer_of_ringEquiv
-- name    : AutomorphicForm.isHaarMeasure_map_and_exists_isHaarMeasure_centralizer_of_ringEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/6dafb339-984b-5079-9b74-e6a2271cc72d
-- title:
--   Haar measures transported along a bicontinuous ring isomorphism
-- statement:
--   Let $A$ and $B$ be commutative topological rings whose topologies make them topological rings, and let $e \colon A \simeq B$ be a ring isomorphism such that both $e$ and $e^{-1}$ are continuous. Write $\hat e =$ `Matrix.GeneralLinearGroup.map e.toRingHom` for the induced group homomorphism $\mathrm{GL}_2(A) \to \mathrm{GL}_2(B)$. All measurable structures are the Borel ones attached to the given topologies: `glBorelOf R` is the Borel $\sigma$-algebra of $\mathrm{GL}_2(R)$, and `centralizerBorel R γ` is the Borel $\sigma$-algebra of the subtype $\mathrm{Cent}_{\mathrm{GL}_2(R)}(\{\gamma\})$ (the centralizer of the singleton set $\{\gamma\}$, carrying the subspace topology). Assume given a Haar measure $\mu$ on $\mathrm{GL}_2(A)$, an element $\gamma \in \mathrm{GL}_2(A)$, and a Haar measure $\tau'$ on the centralizer of $\{\hat e \gamma\}$ in $\mathrm{GL}_2(B)$. The conclusion is the conjunction of two assertions: first, the push-forward $\hat e_* \mu$ is a Haar measure on $\mathrm{GL}_2(B)$; second, there exists a Haar measure $\tau$ on the centralizer of $\{\gamma\}$ in $\mathrm{GL}_2(A)$ whose image in $\mathrm{GL}_2(B)$ under the inclusion followed by $\hat e$ coincides with the image of $\tau'$ under the inclusion of the centralizer of $\{\hat e \gamma\}$ into $\mathrm{GL}_2(B)$, i.e. the two push-forward measures on $\mathrm{GL}_2(B)$ are equal.
--
--   This is the measure-theoretic transport statement underlying comparisons of orbital integrals: an isomorphism of topological rings induces an isomorphism of the topological groups $\mathrm{GL}_2(A)$ and $\mathrm{GL}_2(B)$ carrying the centralizer of $\gamma$ onto that of $\hat e\gamma$, and Haar measures correspond under it. It supplies the matched pairs of measures used in the archimedean matching and twisted-orbital-integral comparisons [`AutomorphicForm.areMatchingArch_central_transfer_of_scalar_of_forall_conjAe_of_forall_algHom`](thm.html#AutomorphicForm.areMatchingArch_central_transfer_of_scalar_of_forall_conjAe_of_forall_algHom) and [`AutomorphicForm.twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom`](thm.html#AutomorphicForm.twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isHaarMeasure_map_and_exists_isHaarMeasure_centralizer_of_ringEquiv.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.isHaarMeasure_map_and_exists_isHaarMeasure_centralizer_of_ringEquiv
    {A B : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)
    (μ : @Measure (GL (Fin 2) A) (glBorelOf A)) (hμ : @Measure.IsHaarMeasure _ _ _ (glBorelOf A) μ)
    (γ : GL (Fin 2) A)
    (τ' : @Measure (Subgroup.centralizer
        ({Matrix.GeneralLinearGroup.map e.toRingHom γ} : Set (GL (Fin 2) B)))
      (centralizerBorel B (Matrix.GeneralLinearGroup.map e.toRingHom γ)))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (centralizerBorel B (Matrix.GeneralLinearGroup.map e.toRingHom γ)) τ') :
    @Measure.IsHaarMeasure _ _ _ (glBorelOf B)
        (@Measure.map _ _ (glBorelOf A) (glBorelOf B) (Matrix.GeneralLinearGroup.map e.toRingHom) μ) ∧
      ∃ τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ),
        @Measure.IsHaarMeasure _ _ _ (centralizerBorel A γ) τ ∧
        (letI := glBorelOf B; letI := centralizerBorel A γ;
          letI := centralizerBorel B (Matrix.GeneralLinearGroup.map e.toRingHom γ);
          Measure.map (fun t : Subgroup.centralizer
              ({Matrix.GeneralLinearGroup.map e.toRingHom γ} : Set (GL (Fin 2) B)) => (t : GL (Fin 2) B)) τ' =
            Measure.map (fun t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) =>
              Matrix.GeneralLinearGroup.map e.toRingHom (t : GL (Fin 2) A)) τ) := by sorry
