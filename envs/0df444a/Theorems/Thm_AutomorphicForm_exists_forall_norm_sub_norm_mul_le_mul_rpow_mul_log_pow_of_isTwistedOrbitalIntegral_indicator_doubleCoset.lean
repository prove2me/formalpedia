-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_norm_sub_norm_mul_le_mul_rpow_mul_log_pow_of_isTwistedOrbitalIntegral_indicator_doubleCoset
-- name    : AutomorphicForm.exists_forall_norm_sub_norm_mul_le_mul_rpow_mul_log_pow_of_isTwistedOrbitalIntegral_indicator_doubleCoset
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/d7713f3d-2096-52e8-9d9d-9abe707b97d3
-- title:
--   One-place double-coset bound for twisted orbital integrals
-- statement:
--   Let $K \subseteq L$ be number fields with $L/K$ Galois, and let $\sigma$ be an automorphism of $L$ over $K$ such that every element of $\mathrm{Gal}(L/K)$ lies in the group of integer powers of $\sigma$. Let $v$ be a nonzero prime of $\mathcal{O}_K$ and $w$ a prime of $\mathcal{O}_L$ lying over $v$. The assertion is the existence of a constant $C \ge 0$ and an exponent $A \in \mathbb{N}$, depending only on these data, with the following property. For every $\rho \in \mathrm{GL}_2(L_w)$ and every $\delta \in \mathrm{GL}_2(L \otimes_K K_v)$ whose off-diagonal entries $\delta_{10}, \delta_{01}$ vanish and whose diagonal entries have distinct $\mathrm{Algebra.norm}$ over $K_v$, and for every Borel measure $\tau'$ on the $\sigma$-twisted centraliser $\{t : t \delta (\sigma_{\mathrm{GL}} t)^{-1} = \delta\}$ of $\delta$ (where $\sigma_{\mathrm{GL}}$ is $\sigma \otimes \mathrm{id}$ applied entrywise) which is Haar and assigns mass $1$ to the intersection of this subgroup with the semi-local integral set $\mathcal{K}_v$ of those $g \in \mathrm{GL}_2(L \otimes_K K_v)$ for which $g$ and $g^{-1}$ have entries in the image of $\mathcal{O}_L \otimes \mathcal{O}_{K_v}$: if $I \in \mathbb{C}$ is a twisted orbital integral, in the sense of [`AutomorphicForm.IsTwistedOrbitalIntegral`](def/AutomorphicForm_TwistedOrbital.html#L366) relative to the Haar measure $\mu'$ on $\mathrm{GL}_2(L \otimes_K K_v)$ normalised by $\mu'(\mathcal{K}_v) = 1$, of the indicator function of the double coset $\mathcal{K}_v \tilde{\rho} \mathcal{K}_v$, where $\tilde{\rho}$ is the semi-local component at $v$ of the adelic matrix obtained by placing $\rho$ at $w$ and the identity elsewhere, then
--   $$\|N\delta_{00} - N\delta_{11}\| \cdot \|I\| \le C \left(\|N\delta_{00} \, N\delta_{11}\| \, \mu'(\mathcal{K}_v \tilde{\rho} \mathcal{K}_v)\right)^{1/2} \left(1 + \log \mu'(\mathcal{K}_v \tilde{\rho} \mathcal{K}_v)\right)^{A},$$
--   the volumes being taken as real numbers.
--
--   This is the one-place form of the local bound on normalised twisted orbital integrals of Hecke double-coset indicators at a finite place $v$, with the test function coming from a single matrix $\rho$ over the completion $L_w$ at a prime $w$ above $v$. It is the input to the global estimate [`AutomorphicForm.exists_forall_lintegral_orbital_doubleCoset_le_mul_prod_rpow_measure`](thm.html#AutomorphicForm.exists_forall_lintegral_orbital_doubleCoset_le_mul_prod_rpow_measure), whose right-hand side carries one factor $\mu'^{1/2}(1+\log\mu')^{A}$ for each place.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_norm_sub_norm_mul_le_mul_rpow_mul_log_pow_of_isTwistedOrbitalIntegral_indicator_doubleCoset.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AdelicDock_LocalEmbedding

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct Pointwise

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.exists_forall_norm_sub_norm_mul_le_mul_rpow_mul_log_pow_of_isTwistedOrbitalIntegral_indicator_doubleCoset
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ A : ℕ,
    ∀ (ρ : GL (Fin 2) (w.1.adicCompletion L)),
    ∀ (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)),
      (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 0 = 0 → (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 1 = 0 →
      Algebra.norm (v.adicCompletion K) ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0) ≠
        Algebra.norm (v.adicCompletion K) ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1) →
    ∀ (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)
        (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ)),
      @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ' →
      τ' (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v) = 1 →
    ∀ I : ℂ, AutomorphicForm.IsTwistedOrbitalIntegral K L v σ δ τ'
        ((AutomorphicForm.semiLocalIntegralSet K L v *
            {(AutomorphicForm.semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L w.1 ρ))} *
            AutomorphicForm.semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))) I →
      ‖Algebra.norm (v.adicCompletion K) ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0) -
          Algebra.norm (v.adicCompletion K) ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1)‖ * ‖I‖ ≤
        C * (‖Algebra.norm (v.adicCompletion K) ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0) *
              Algebra.norm (v.adicCompletion K) ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1)‖ *
            (AutomorphicForm.semiLocalHaar K L v
              (AutomorphicForm.semiLocalIntegralSet K L v *
            {(AutomorphicForm.semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L w.1 ρ))} *
            AutomorphicForm.semiLocalIntegralSet K L v)).toReal) ^ ((1 : ℝ) / 2) *
          (1 + Real.log (AutomorphicForm.semiLocalHaar K L v
              (AutomorphicForm.semiLocalIntegralSet K L v *
            {(AutomorphicForm.semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L w.1 ρ))} *
            AutomorphicForm.semiLocalIntegralSet K L v)).toReal) ^ A := by sorry
