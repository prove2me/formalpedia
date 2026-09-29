-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_withDensity_norm_inv_setOf_norm_mem_and_mul_sigmaTensor_eq_mul_mul_le
-- name    : AutomorphicForm.exists_forall_withDensity_norm_inv_setOf_norm_mem_and_mul_sigmaTensor_eq_mul_mul_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/57cdf887-8fca-52d4-96bc-e814d99e8963
-- title:
--   Uniform fibre-volume bound for σ-twisted conjugation on L⊗_K Kᵥ
-- statement:
--   Let $K$ and $L$ be number fields with $L$ an algebra over $K$ and $L/K$ Galois, and let $\sigma \in \mathrm{Gal}(L/K)$ be such that every $\tau \in \mathrm{Gal}(L/K)$ lies in the subgroup of integer powers of $\sigma$ (so $L/K$ is cyclic with generator $\sigma$). Let $v$ be a nonzero prime of $\mathcal{O}_K$, write $K_v$ for the $v$-adic completion, and set $E = L \otimes_K K_v$, equipped with a measurable structure that is the Borel structure of its topology; let $\nu$ be an additive Haar measure on $E$. Let $W \subseteq K_v$ be compact with $0 \notin W$, and let $U \subseteq E$ be compact and consist of units. Then there is a constant $C \in [0,\infty]$ with $C \neq \infty$ such that for every unit $A \in E^{\times}$ and every $p \in E$, the measure $\nu$ weighted by the density $b \mapsto \|N_{E/K_v}(b)\|^{-1}$ (as an element of $[0,\infty]$, via `ENNReal.ofReal`) assigns to the set of those $b \in E$ which are units, whose norm $N_{E/K_v}(b)$ lies in $W$, and for which $A \cdot (\sigma \otimes \mathrm{id}_{K_v})(b) = b\,p\,u$ for some $u \in U$, a value at most $C$. Here $\sigma \otimes \mathrm{id}_{K_v}$ is the ring endomorphism [`AutomorphicForm.sigmaTensor`](def/AutomorphicForm_TwistedOrbital.html#L199) of $E$ obtained by base change of $\sigma$ along $K \to K_v$. The bound is uniform in $A$ and $p$, and no measurability hypothesis on the set is required.
--
--   This is the fibre-volume input for the analysis of $\sigma$-twisted orbital integrals on $\mathrm{GL}_2$ over the semilocal algebra $L \otimes_K K_v$: modulo the central $K_v^{\times}$-direction the set in question is the preimage of a translate of $U$ under $b \mapsto \sigma(b)/b$, and the condition $N(b) \in W$ with $0 \notin W$ confines $b$ to a window of bounded logarithmic width. It is cited by [`AutomorphicForm.exists_forall_norm_sub_norm_mul_le_mul_rpow_mul_log_pow_of_isTwistedOrbitalIntegral_indicator_semiLocalIntegralSet_mul_mul`](thm.html#AutomorphicForm.exists_forall_norm_sub_norm_mul_le_mul_rpow_mul_log_pow_of_isTwistedOrbitalIntegral_indicator_semiLocalIntegralSet_mul_mul), the estimate for twisted orbital integrals of the relevant indicator functions used in the cyclic base change step towards the Langlands–Tunnell theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_withDensity_norm_inv_setOf_norm_mem_and_mul_sigmaTensor_eq_mul_mul_le.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_ConstantTerm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions ENNReal Pointwise
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.exists_forall_withDensity_norm_inv_setOf_norm_mem_and_mul_sigmaTensor_eq_mul_mul_le
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
    (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure]
    (W : Set (v.adicCompletion K)) (hW : IsCompact W) (hW0 : (0 : v.adicCompletion K) ∉ W)
    (U : Set (L ⊗[K] v.adicCompletion K)) (hU : IsCompact U) (hU1 : ∀ u ∈ U, IsUnit u) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (A : (L ⊗[K] v.adicCompletion K)ˣ) (p : L ⊗[K] v.adicCompletion K),
      ν.withDensity (fun b => ENNReal.ofReal ‖Algebra.norm (v.adicCompletion K) b‖⁻¹)
        {b : L ⊗[K] v.adicCompletion K | IsUnit b ∧ Algebra.norm (v.adicCompletion K) b ∈ W ∧
          ∃ u ∈ U, (A : L ⊗[K] v.adicCompletion K) * AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ b =
            b * p * u} ≤ C := by sorry
