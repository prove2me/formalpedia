-- Prove2me | Theorems.Thm_AutomorphicForm_lintegral_comp_conj_twistedCentralizer_eq_mul_inv_one_sub_mul_inv_one_sub_of_map_eq_smul_map_toTensorGL_localHaar
-- name    : AutomorphicForm.lintegral_comp_conj_twistedCentralizer_eq_mul_inv_one_sub_mul_inv_one_sub_of_map_eq_smul_map_toTensorGL_localHaar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/75a52fc0-89ff-57ce-bf38-bb8e13dfd2c0
-- title:
--   Twisted-centralizer integral equals the local zeta factor
-- statement:
--   Let $K \subseteq L$ be number fields with $L$ an algebra over $K$, let $\sigma$ be a $K$-algebra automorphism of $L$, let $v$ be a nonzero prime of $\mathcal{O}_K$ with completion $K_v$, and set $G = \mathrm{GL}_2(L \otimes_K K_v)$, all groups being equipped with their Borel $\sigma$-algebras. Fix $\delta \in G$ and let $T'_\delta = \{t \in G : t\,\delta\,\sigma(t)^{-1} = \delta\}$ be the $\sigma$-twisted centralizer of $\delta$, where $\sigma$ acts on $G$ entrywise through the automorphism of $L \otimes_K K_v$ induced by $\sigma$. Let $\tau'$ be a measure on $T'_\delta$, let $y \in G$ and $t_v \in [0,\infty]$, and assume that the push-forward of $\tau'$ along $t \mapsto y^{-1} t y$ equals $t_v$ times the push-forward of the Haar measure of $\mathrm{GL}_2(K_v)$ normalised to give mass $1$ to the subgroup of matrices with entries and inverse entries in $\mathcal{O}_v$, along the map $g \mapsto 1 \otimes g$. Let $s \in \mathbb{R}$ and let $\Psi : G \to [0,\infty]$ be Borel measurable with $\Psi(1 \otimes g) = \|\det g\|_v^{\,s}$ when all entries of $g \in \mathrm{GL}_2(K_v)$ lie in $\mathcal{O}_v$, and $\Psi(1 \otimes g) = 0$ otherwise. Then, with $q_v$ the absolute norm of $v$, $$\int_{T'_\delta} \Psi(y^{-1} t y)\, d\tau'(t) = t_v \cdot (1 - q_v^{-s})^{-1}(1 - q_v^{1-s})^{-1},$$ an identity in $[0,\infty]$, subtraction and inversion being those of the extended nonnegative reals.
--
--   This is the evaluation of the local orbital integral at a place of good behaviour: the twisted-centralizer integral of a local zeta integrand is the local Euler factor $(1-q_v^{-s})^{-1}(1-q_v^{1-s})^{-1}$ of $\mathrm{GL}_2$ at $v$, times the normalising constant $t_v$. It is stated in push-forward form, so that it is independent of how the global integrand is factorised, and is used in the assembly of the Euler product for the twisted orbital integral over all places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_lintegral_comp_conj_twistedCentralizer_eq_mul_inv_one_sub_mul_inv_one_sub_of_map_eq_smul_map_toTensorGL_localHaar.lean

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory Filter NumberField NumberField.AdelicHaar NumberField.AdelicFourier NumberField.AdelicBox
  NumberField.TateGlobal IsDedekindDomain AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions ENNReal Topology

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

theorem AutomorphicForm.lintegral_comp_conj_twistedCentralizer_eq_mul_inv_one_sub_mul_inv_one_sub_of_map_eq_smul_map_toTensorGL_localHaar
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K))
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (τ' : Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ))
    (y : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (tv : ℝ≥0∞)
    (hτ' : (letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
       letI := AutomorphicForm.localGLBorel K v
       Measure.map (fun t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ) =>
            y⁻¹ * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * y) τ' =
          tv • Measure.map (AutomorphicForm.toTensorGL K L (v.adicCompletion K)) (AutomorphicForm.localHaar K v)))
    (s : ℝ) (Ψ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℝ≥0∞)
    (hΨm : Measurable[AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)] Ψ)
    (hΨ1 : ∀ g : GL (Fin 2) (v.adicCompletion K),
      (∀ i j, (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j ∈ v.adicCompletionIntegers K) →
        Ψ (AutomorphicForm.toTensorGL K L (v.adicCompletion K) g) =
          ((‖((Matrix.GeneralLinearGroup.det g : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖₊ : ℝ≥0∞) ^ s))
    (hΨ0 : ∀ g : GL (Fin 2) (v.adicCompletion K),
      ¬ (∀ i j, (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j ∈ v.adicCompletionIntegers K) →
        Ψ (AutomorphicForm.toTensorGL K L (v.adicCompletion K) g) = 0) :
    ∫⁻ t, Ψ (y⁻¹ * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * y) ∂τ' =
      tv * ((1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (-s))⁻¹ *
        (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - s))⁻¹) := by sorry
