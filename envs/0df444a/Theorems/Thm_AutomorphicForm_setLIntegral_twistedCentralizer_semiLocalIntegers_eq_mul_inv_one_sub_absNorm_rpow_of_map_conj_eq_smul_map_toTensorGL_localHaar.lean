-- Prove2me | Theorems.Thm_AutomorphicForm_setLIntegral_twistedCentralizer_semiLocalIntegers_eq_mul_inv_one_sub_absNorm_rpow_of_map_conj_eq_smul_map_toTensorGL_localHaar
-- name    : AutomorphicForm.setLIntegral_twistedCentralizer_semiLocalIntegers_eq_mul_inv_one_sub_absNorm_rpow_of_map_conj_eq_smul_map_toTensorGL_localHaar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/9ddf6fd7-7c05-538e-bf06-f4b5c29fda60
-- title:
--   Unramified local zeta factor on a twisted centralizer
-- statement:
--   Let $K \subseteq L$ be number fields, $\sigma$ a $K$-automorphism of $L$, $v$ a nonzero prime of $\mathcal{O}_K$ with completion $K_v$, and $\delta \in \mathrm{GL}_2(L \otimes_K K_v)$. Let $T$ denote the $\sigma$-twisted centraliser of $\delta$, the subgroup of $t \in \mathrm{GL}_2(L \otimes_K K_v)$ with $t\,\delta\,(\sigma_{\mathrm{GL}} t)^{-1} = \delta$, where $\sigma_{\mathrm{GL}}$ acts entrywise through $\sigma \otimes \mathrm{id}$; $T$ carries the Borel $\sigma$-algebra of its subspace topology. Let $\tau$ be a Haar measure on $T$, let $y \in \mathrm{GL}_2(L \otimes_K K_v)$ and $c \in [0,\infty]$, and assume: (i) the pushforward of $\tau$ along $t \mapsto y^{-1} t y$ equals $c$ times the pushforward, along $g \mapsto 1 \otimes g$, of the Haar measure on $\mathrm{GL}_2(K_v)$ normalised to give mass one to the set of $g$ with $g$ and $g^{-1}$ having all entries in $\mathcal{O}_v$; (ii) $\tau$ assigns mass $c$ to the set of $t \in T$ such that $t$ and $t^{-1}$ have all entries in the image of $\mathcal{O}_L \otimes_{\mathcal{O}_K} \mathcal{O}_v$ in $L \otimes_K K_v$. Let $a \in \mathbb{R}$ and let $N : T \to [0,\infty]$ satisfy $N(t) = \|s\|^a$ whenever $\det t$ is the image of $s \in K_v^\times$ under $x \mapsto 1 \otimes x$. Then, with $q = \mathrm{absNorm}(v)$,
--   $$\int_{\{t \in T \,:\, \text{all entries of } t \text{ lie in the image of } \mathcal{O}_L \otimes_{\mathcal{O}_K} \mathcal{O}_v\}} N(t)\,d\tau = c\,(1-q^{-a})^{-1}(1-q^{1-a})^{-1},$$
--   computed in $[0,\infty]$, the integration set being cut out by a condition on $t$ alone.
--
--   This is the local Euler factor, at a finite place where the relevant algebra is split, arising in the orbital-integral computation for a twisted centraliser: the integral of the $a$-th power of the absolute value of the reduced norm over the integral elements. It feeds the global computation of such integrals as a product of archimedean, Dedekind zeta and finite-place contributions, and the normalised special case in which $\tau$ gives mass one to the integral units.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_setLIntegral_twistedCentralizer_semiLocalIntegers_eq_mul_inv_one_sub_absNorm_rpow_of_map_conj_eq_smul_map_toTensorGL_localHaar.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions ENNReal NNReal

attribute [local instance] AutomorphicForm.twistedCentralizerBorel

theorem AutomorphicForm.setLIntegral_twistedCentralizer_semiLocalIntegers_eq_mul_inv_one_sub_absNorm_rpow_of_map_conj_eq_smul_map_toTensorGL_localHaar
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K))
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (τ : Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ))
    (hτ : τ.IsHaarMeasure)
    (y : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (c : ℝ≥0∞)
    (hy : letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
      letI := AutomorphicForm.localGLBorel K v
      Measure.map (fun t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ) =>
          y⁻¹ * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * y) τ =
        c • Measure.map (AutomorphicForm.toTensorGL K L (v.adicCompletion K)) (AutomorphicForm.localHaar K v))
    (hU : τ (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v) = c)
    (a : ℝ) (N : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ) → ℝ≥0∞)
    (hN : ∀ (t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)) (s : (v.adicCompletion K)ˣ),
      Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
        Units.map (Algebra.TensorProduct.includeRight :
          v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s →
      N t = ((‖(s : v.adicCompletion K)‖₊ : ℝ≥0∞) ^ a)) :
    ∫⁻ t in {t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ) |
        ∀ i j, ((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
          Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) i j ∈ AutomorphicForm.semiLocalIntegers K L v},
        N t ∂τ =
      c * ((1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (-a))⁻¹ *
        (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - a))⁻¹) := by sorry
