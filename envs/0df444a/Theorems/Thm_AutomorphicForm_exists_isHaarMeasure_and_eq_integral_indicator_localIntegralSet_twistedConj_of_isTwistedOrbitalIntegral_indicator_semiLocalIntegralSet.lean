-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isHaarMeasure_and_eq_integral_indicator_localIntegralSet_twistedConj_of_isTwistedOrbitalIntegral_indicator_semiLocalIntegralSet
-- name    : AutomorphicForm.exists_isHaarMeasure_and_eq_integral_indicator_localIntegralSet_twistedConj_of_isTwistedOrbitalIntegral_indicator_semiLocalIntegralSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/d8e4f888-fd8e-50db-b5b7-f1d4863026c0
-- title:
--   Descent of a semi-local twisted orbital integral to one place
-- statement:
--   Let $K \subseteq L$ be number fields, $\sigma$ a $K$-algebra automorphism of $L$, $v$ a height-one prime of $\mathcal O_K$ and $w$ a height-one prime of $\mathcal O_L$ lying over $v$, with completions $K_v$ and $L_w$. Let $\theta$ be a $K_v$-algebra automorphism of $L_w$ and $\Psi \colon L \otimes_K K_v \to L_w^{m+1}$ a $K_v$-algebra isomorphism such that (a) for all $z$ the coordinates of $\Psi((\sigma \otimes 1)z)$ are $(\Psi z)_1, \dots, (\Psi z)_m, \theta((\Psi z)_0)$, and (b) $z$ lies in [`AutomorphicForm.semiLocalIntegers K L v`](def/AutomorphicForm_TwistedOrbital.html#L98), the image of $\mathcal O_L \otimes \mathcal O_v$ in $L \otimes_K K_v$, exactly when every coordinate $(\Psi z)_j$ lies in $\mathcal O_w$. Let $\delta \in \mathrm{GL}_2(L \otimes_K K_v)$ be such that every element $t$ of the twisted centraliser $T = \{t : t\delta(\sigma \otimes 1)(t)^{-1} = \delta\}$ has all its matrix entries in the image of $K_v \to L \otimes_K K_v$, $a \mapsto 1 \otimes a$. Let $\tau'$ be a Haar measure on $T$, with its Borel $\sigma$-algebra, giving mass $1$ to the part of $T$ lying in [`AutomorphicForm.semiLocalIntegralSet K L v`](def/AutomorphicForm_TwistedOrbital.html#L136) (the integral units of $L\otimes_K K_v$), and let $I \in \mathbb C$ be a value of the $\sigma$-twisted orbital integral at $\delta$ of the indicator of that integral set, taken with respect to [`AutomorphicForm.semiLocalHaar K L v`](def/AutomorphicForm_TwistedOrbital.html#L169) and $\tau'$. Finally let $\nu \in \mathrm{GL}_2(L_w)$ be the product $\delta_0\delta_1\cdots\delta_m$ of the images of $\delta$ under the $m+1$ coordinate maps $\mathrm{GL}_2(L \otimes_K K_v) \to \mathrm{GL}_2(L_w)$ induced by $\Psi$, in that order. Then there exist a Haar measure $\tau_0$, for the Borel $\sigma$-algebra, on the $\theta$-twisted centraliser $\{t \in \mathrm{GL}_2(L_w) : t\nu\theta(t)^{-1} = \nu\}$ (with $\theta$ acting entrywise) giving mass $1$ to the part of that subgroup lying in [`AutomorphicForm.localIntegralSet L w`](def/AutomorphicForm_LocalOrbitalBase.html#L100), and a nonnegative, Borel measurable, compactly supported $s \colon \mathrm{GL}_2(L_w) \to \mathbb R$ with $\int s(tx) \, d\tau_0(t) = 1$ for every $x$ with $x^{-1}\nu\theta(x) \in$ [`AutomorphicForm.localIntegralSet L w`](def/AutomorphicForm_LocalOrbitalBase.html#L100), such that either $I = 0$ or $I$ equals the integral over $\mathrm{GL}_2(L_w)$, against the normalised Haar measure [`AutomorphicForm.localHaar L w`](def/AutomorphicForm_LocalOrbitalBase.html#L168), of the indicator of [`AutomorphicForm.localIntegralSet L w`](def/AutomorphicForm_LocalOrbitalBase.html#L100) evaluated at $x^{-1}\nu\theta(x)$ times $s(x)$. Thus the identification of $I$ with a local $\theta$-twisted orbital integral at $\nu$ is asserted only up to the alternative $I = 0$.
--
--   This is the descent step for twisted orbital integrals in the theory of base change for $\mathrm{GL}_2$: under the decomposition $L \otimes_K K_v \cong \prod_{w' \mid v} L_{w'}$ encoded by $\Psi$, the twisted orbital integral of the unit of the semi-local Hecke algebra above $v$ is rewritten as a twisted orbital integral at the partial norm $\nu$ of $\delta$ over the single completion $L_w$. It feeds the comparison [`AutomorphicForm.norm_sub_norm_mul_le_of_isTwistedOrbitalIntegral_indicator_semiLocalIntegralSet_of_ramificationIdx_eq_one`](thm.html#AutomorphicForm.norm_sub_norm_mul_le_of_isTwistedOrbitalIntegral_indicator_semiLocalIntegralSet_of_ramificationIdx_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isHaarMeasure_and_eq_integral_indicator_localIntegralSet_twistedConj_of_isTwistedOrbitalIntegral_indicator_semiLocalIntegralSet.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_LocalOrbitalBase

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_isHaarMeasure_and_eq_integral_indicator_localIntegralSet_twistedConj_of_isTwistedOrbitalIntegral_indicator_semiLocalIntegralSet
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L)) {m : ℕ}
    (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (Ψ : (L ⊗[K] v.adicCompletion K) ≃ₐ[v.adicCompletion K] (Fin (m + 1) → w.1.adicCompletion L))
    (hΨσ : ∀ z : L ⊗[K] v.adicCompletion K,
      (∀ k : Fin m, Ψ (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ z) k.castSucc = Ψ z k.succ) ∧
        Ψ (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ z) (Fin.last m) = θ (Ψ z 0))
    (hΨint : ∀ z : L ⊗[K] v.adicCompletion K,
      z ∈ AutomorphicForm.semiLocalIntegers K L v ↔ ∀ j, Ψ z j ∈ w.1.adicCompletionIntegers L)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hT : ∀ t ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ, ∀ p q,
      ((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) p q ∈
        Set.range (Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K))
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)
        (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ')
    (hτ'1 : τ' (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v) = 1)
    (I : ℂ) (hI : AutomorphicForm.IsTwistedOrbitalIntegral K L v σ δ τ'
        ((AutomorphicForm.semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))) I)
    (ν : GL (Fin 2) (w.1.adicCompletion L))
    (hν : ν = (List.ofFn fun j : Fin (m + 1) => Matrix.GeneralLinearGroup.map
        ((Pi.evalRingHom (fun _ : Fin (m + 1) => w.1.adicCompletion L) j).comp
          (Ψ : L ⊗[K] v.adicCompletion K →+* (Fin (m + 1) → w.1.adicCompletion L))) δ).prod) :
    ∃ (τ₀ : @Measure (AutomorphicForm.sigmaCentralizer
          (Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom) ν) (borel _))
      (s : GL (Fin 2) (w.1.adicCompletion L) → ℝ),
      @Measure.IsHaarMeasure _ _ _ (borel _) τ₀ ∧
      τ₀ {t | (t : GL (Fin 2) (w.1.adicCompletion L)) ∈ AutomorphicForm.localIntegralSet L w.1} = 1 ∧
      (∀ x, 0 ≤ s x) ∧ Measurable[AutomorphicForm.localGLBorel L w.1] s ∧ HasCompactSupport s ∧
      (∀ x : GL (Fin 2) (w.1.adicCompletion L),
        x⁻¹ * ν * Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom x ∈ AutomorphicForm.localIntegralSet L w.1 →
          ∫ t : AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom) ν,
            s ((t : GL (Fin 2) (w.1.adicCompletion L)) * x) ∂τ₀ = 1) ∧
      (I = 0 ∨
        I = ∫ x : GL (Fin 2) (w.1.adicCompletion L),
          (AutomorphicForm.localIntegralSet L w.1).indicator (fun _ => (1 : ℂ))
              (x⁻¹ * ν * Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom x) * (s x : ℂ)
            ∂(AutomorphicForm.localHaar L w.1)) := by sorry
