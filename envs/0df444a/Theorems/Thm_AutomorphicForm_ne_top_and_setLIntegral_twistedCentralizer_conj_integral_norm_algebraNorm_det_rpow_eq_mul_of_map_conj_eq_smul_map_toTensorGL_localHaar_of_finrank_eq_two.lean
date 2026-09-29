-- Prove2me | Theorems.Thm_AutomorphicForm_ne_top_and_setLIntegral_twistedCentralizer_conj_integral_norm_algebraNorm_det_rpow_eq_mul_of_map_conj_eq_smul_map_toTensorGL_localHaar_of_finrank_eq_two
-- name    : AutomorphicForm.ne_top_and_setLIntegral_twistedCentralizer_conj_integral_norm_algebraNorm_det_rpow_eq_mul_of_map_conj_eq_smul_map_toTensorGL_localHaar_of_finrank_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/2634827f-16cf-58fa-b3a7-24b2bfba3caf
-- title:
--   Local zeta integral over a twisted centraliser, first-kind normalisation
-- statement:
--   Let $K \subseteq L$ be number fields with $[L:K] = 2$, let $\sigma$ be a $K$-algebra automorphism of $L$, let $v$ be a nonzero prime of $\mathcal{O}_K$ with completion $K_v$, and put $A = L \otimes_K K_v$. Let $\delta \in \mathrm{GL}_2(A)$ and let $T'_\delta$ be the twisted centraliser, i.e. the subgroup of $t \in \mathrm{GL}_2(A)$ with $t\,\delta\,(\sigma t)^{-1} = \delta$, where $\sigma$ acts entrywise through the induced automorphism of $A$; $T'_\delta$ carries its Borel structure. Let $\tau'$ be a Haar measure on $T'_\delta$, let $y \in \mathrm{GL}_2(A)$ and $t_v \in [0,\infty]$, and assume that the push-forward of $\tau'$ along $t \mapsto y^{-1} t y$ equals $t_v$ times the push-forward of the Haar measure of $\mathrm{GL}_2(K_v)$ normalised to give mass $1$ to the compact open set of matrices with entries in $\mathcal{O}_v$, along the entrywise base-change map $\mathrm{GL}_2(K_v) \to \mathrm{GL}_2(A)$ (all measures for the Borel structures). Then $t_v \neq \infty$ and, for every real $s' \geq 1$, the lower integral of $\lVert N_{A/K_v}(\det t)\rVert^{s'}$ over $\{t \in T'_\delta : y^{-1} t y$ is the base change of some $g \in \mathrm{GL}_2(K_v)$ with all entries in $\mathcal{O}_v\}$ with respect to $\tau'$ equals $t_v\,(1 - q_v^{-2s'})^{-1}(1 - q_v^{1-2s'})^{-1}$, where $q_v$ is the absolute norm of $v$.
--
--   This is the local zeta computation attached to a place $v$ at which the twisted centraliser measure has been normalised through a conjugator $y$: the integral of the norm of the determinant over the part of the twisted centraliser meeting the standard maximal compact produces the local factor $(1-q_v^{-2s'})^{-1}(1-q_v^{1-2s'})^{-1}$ scaled by the mass $t_v$, together with the finiteness of that mass. It feeds the choice of level in [`AutomorphicForm.exists_finset_level_isOpen_isCompact_box_subset_indicator_mulVec_eq_prod_indicator_tensorPlace_of_normString_eq_toTensorGL_centralScalar_of_finrank_eq_two`](thm.html#AutomorphicForm.exists_finset_level_isOpen_isCompact_box_subset_indicator_mulVec_eq_prod_indicator_tensorPlace_of_normString_eq_toTensorGL_centralScalar_of_finrank_eq_two), where the Euler product of these local factors is assembled.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_ne_top_and_setLIntegral_twistedCentralizer_conj_integral_norm_algebraNorm_det_rpow_eq_mul_of_map_conj_eq_smul_map_toTensorGL_localHaar_of_finrank_eq_two.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory Filter NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions ENNReal NNReal Topology

attribute [local instance] AutomorphicForm.twistedCentralizerBorel

open scoped Classical

theorem AutomorphicForm.ne_top_and_setLIntegral_twistedCentralizer_conj_integral_norm_algebraNorm_det_rpow_eq_mul_of_map_conj_eq_smul_map_toTensorGL_localHaar_of_finrank_eq_two
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K))
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (τ' : Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)) (hτ'h : τ'.IsHaarMeasure)
    (y : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (tv : ℝ≥0∞)
    (hτ' : (letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
       letI := AutomorphicForm.localGLBorel K v
       Measure.map (fun t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ) =>
            y⁻¹ * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * y) τ' =
          tv • Measure.map (AutomorphicForm.toTensorGL K L (v.adicCompletion K)) (AutomorphicForm.localHaar K v))) :
    tv ≠ ⊤ ∧
    ∀ s' : ℝ, 1 ≤ s' →
      ∫⁻ t in {t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ) |
          ∃ g : GL (Fin 2) (v.adicCompletion K),
            (∀ i j, (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j ∈ v.adicCompletionIntegers K) ∧
            y⁻¹ * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * y =
              AutomorphicForm.toTensorGL K L (v.adicCompletion K) g},
        ENNReal.ofReal (‖Algebra.norm (v.adicCompletion K) (Matrix.det ((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
            Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)))‖ ^ s') ∂τ' =
        tv * ((1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (-(2 * s')))⁻¹ *
          (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - 2 * s'))⁻¹) := by sorry
