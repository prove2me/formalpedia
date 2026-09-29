-- Prove2me | Theorems.Thm_AutomorphicForm_lintegral_norm_inv_mul_torusSection_mul_eq_of_forall_mul_eq
-- name    : AutomorphicForm.lintegral_norm_inv_mul_torusSection_mul_eq_of_forall_mul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/e3031304-5d9e-5ef4-9bae-f57a14a41488
-- title:
--   Torus sections give equal ‖N‖⁻¹-weighted integrals
-- statement:
--   Let $L/K$ be an extension of number fields that is finite and Galois, and let $\sigma \in \mathrm{Gal}(L/K)$ be such that every element of the Galois group lies in $\langle \sigma \rangle$. Fix a nonzero prime $v$ of $\mathcal{O}_K$, write $K_v$ for the $v$-adic completion and $E = L \otimes_K K_v$, equipped with a measurable structure that is the Borel structure of its topology, and let $\nu$ be an additive Haar measure on $E$. Let $\alpha, \beta \in E^{\times}$ and $a, b \in K_v^{\times}$ with $a \neq b$, and suppose that the norm string of $\delta = \mathrm{diag}(\alpha,\beta) \in \mathrm{GL}_2(E)$, that is the product $\prod_{i=0}^{[L:K]-1} \sigma^{i}(\delta)$ of the iterates of the entrywise action of $\sigma$ on $\mathrm{GL}_2(E)$, equals the image of $\mathrm{diag}(a,b)$ under the map $\mathrm{GL}_2(K_v) \to \mathrm{GL}_2(E)$ induced by $x \mapsto 1 \otimes x$. Let $T = \{t \in \mathrm{GL}_2(E) : t\,\delta\,\sigma(t)^{-1} = \delta\}$ be the $\sigma$-twisted centraliser of $\delta$, carrying its Borel structure, and let $\tau'$ be a Haar measure on $T$. Let $\beta_1, \beta_2 : E \times E \to \mathbb{R}$ be measurable and nonnegative and satisfy, for every pair $p = (p_1,p_2)$ with $p_1$ and $p_2$ units, $\int_T \beta_i(t_{00}p_1, t_{11}p_2)\,d\tau'(t) = 1$, where $t_{00}, t_{11}$ are the diagonal entries of $t$. Let $H : E \times E \to [0,\infty]$ be measurable and invariant under $p \mapsto (t_{00}p_1, t_{11}p_2)$ for all $t \in T$. Then the lower Lebesgue integrals with respect to $\nu \times \nu$ of the two functions that take the value $\|N_{E/K_v}(p_1p_2)\|^{-1}\beta_i(p) \cdot H(p)$ at pairs $p$ with both coordinates units and $0$ elsewhere ($i = 1, 2$) are equal.
--
--   This is the statement that the weighted measure $\|N_{E/K_v}(p_1p_2)\|^{-1}\,d\nu\,d\nu$ on pairs of units, integrated against a torus-invariant function, does not see which normalised torus section $\beta_i$ is inserted; it is the substitution step in Weil-style unfolding of twisted orbital integrals for the diagonal torus attached to $\mathrm{diag}(\alpha,\beta)$. It feeds the Iwasawa-decomposition form of the twisted weighted orbital identity for exact diagonal lifts, which cites it to replace the section implicit in an orbital value by a chosen one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_lintegral_norm_inv_mul_torusSection_mul_eq_of_forall_mul_eq.lean

import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open LanglandsTunnell.CubicInduction (diagUnits2)
open scoped TensorProduct TensorProduct.RightActions Classical

theorem AutomorphicForm.lintegral_norm_inv_mul_torusSection_mul_eq_of_forall_mul_eq
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
    (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure]
    (α β : (L ⊗[K] v.adicCompletion K)ˣ) (a b : (v.adicCompletion K)ˣ) (hab : a ≠ b)
    (hN : AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
      AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a b))
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α β))
      (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)))
    (hτ' : @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)) τ')
    (β₁ β₂ : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K) → ℝ) (hβ₁m : Measurable β₁) (hβ₂m : Measurable β₂)
    (hβ₁0 : ∀ p, 0 ≤ β₁ p) (hβ₂0 : ∀ p, 0 ≤ β₂ p)
    (hβ₁ : ∀ p : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K), IsUnit p.1 → IsUnit p.2 →
      @integral _ ℝ _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)) τ'
        (fun t => β₁ ((((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0) * p.1, (((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1) * p.2)) = 1)
    (hβ₂ : ∀ p : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K), IsUnit p.1 → IsUnit p.2 →
      @integral _ ℝ _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)) τ'
        (fun t => β₂ ((((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0) * p.1, (((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1) * p.2)) = 1)
    (H : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K) → ENNReal) (hHm : Measurable H)
    (hH : ∀ (t : AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α β)) (p : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K)),
      H ((((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0) * p.1, (((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1) * p.2) = H p) :
    ∫⁻ p : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K), (if IsUnit p.1 ∧ IsUnit p.2 then
        ENNReal.ofReal (‖Algebra.norm (v.adicCompletion K) (p.1 * p.2)‖⁻¹ * β₁ p) * H p else 0) ∂(ν.prod ν) =
    ∫⁻ p : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K), (if IsUnit p.1 ∧ IsUnit p.2 then
        ENNReal.ofReal (‖Algebra.norm (v.adicCompletion K) (p.1 * p.2)‖⁻¹ * β₂ p) * H p else 0) ∂(ν.prod ν) := by sorry
