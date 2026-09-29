-- Prove2me | Theorems.Thm_AutomorphicForm_exists_pos_forall_integral_twistedCentralizer_eq_mul_integral_tensorArch_mul_prod_integral_tensorPlace_of_diagonal
-- name    : AutomorphicForm.exists_pos_forall_integral_twistedCentralizer_eq_mul_integral_tensorArch_mul_prod_integral_tensorPlace_of_diagonal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/9fd3cd0c-896d-52ce-baaa-1d6b033c9e6f
-- title:
--   Class-uniform constant in the twisted torus factorisation
-- statement:
--   Let $K$ and $L$ be number fields with $L/K$ finite Galois, and let $\sigma \in \mathrm{Gal}(L/K)$ be such that every element of the Galois group is an integral power of $\sigma$ (so the extension is cyclic with generator $\sigma$). Fix Haar measures $\nu_K$ on $(\mathbb{A}_K)^\times$ and $\nu_A$ on $(K_\infty)^\times$, for the Borel structures, and a real $c_\tau > 0$. The assertion is the existence of a real $c_T > 0$ with the following property, uniformly in all the data that follow. Let $t \in \mathrm{GL}_2(L)$ be diagonal (entries $(1,0)$ and $(0,1)$ vanish) with $\mathrm{Norm}_{K}(t_{00}/t_{11}) \neq 1$, and let $\delta \in \mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$ be mapped by [`AutomorphicForm.baseChangeGL`](def/AutomorphicForm_BaseChangePlaces.html#L69) (induced by the ring isomorphism $L \otimes_K \mathbb{A}_K \cong \mathbb{A}_L$) to the image of $t$ under $\mathrm{GL}_2(L) \to \mathrm{GL}_2(\mathbb{A}_L)$. Let $\tau$ be a Haar measure, for the Borel structure, on the $\sigma$-twisted centraliser of $\delta$ in $\mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$, subject to the hypothesis that for every function $g : \mathrm{GL}_2(L \otimes_K \mathbb{A}_K) \to \mathbb{C}$ one has $\int g(s)\,d\tau = c_\tau \int g(\mathrm{diag}(x,y))\,d(\nu_K \times \nu_K)$, the diagonal matrix being formed by `diagUnits2` and pushed into $\mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$ by [`AutomorphicForm.toTensorGL`](def/AutomorphicForm_TwistedOrbital.html#L71); let $\tau_a$ be a Haar measure on the $\sigma$-twisted centraliser of [`AutomorphicForm.tensorArch K L δ`](def/AutomorphicForm_BaseChangePlaces.html#L46) in $\mathrm{GL}_2(L \otimes_K K_\infty)$ satisfying the same identity with constant $1$ against $\nu_A \times \nu_A$; and for each finite place $v$ of $K$ let $\tau_f(v)$ be a Haar measure on the $\sigma$-twisted centraliser of [`AutomorphicForm.tensorPlace K L v δ`](def/AutomorphicForm_BaseChangePlaces.html#L49) in $\mathrm{GL}_2(L \otimes_K K_v)$ assigning mass $1$ to the set of its elements lying in [`AutomorphicForm.semiLocalIntegralSet K L v`](def/AutomorphicForm_TwistedOrbital.html#L136), that is, those $g$ with $g$ and $g^{-1}$ having all entries in the semilocal integers at $v$. Then for every finite set $S$ of finite places and all functions $W$, $W_a$ and $W_{S,v}$ on the respective general linear groups, with $W_a$ almost everywhere strongly measurable for $\tau_a$ and $W_{S,v}$ almost everywhere strongly measurable for $\tau_f(v)$ for $v \in S$, such that $W(t) = W_a(\mathrm{tensorArch}\,t) \cdot \prod_{v \in S} W_{S,v}(\mathrm{tensorPlace}_v\,t)$ whenever $\mathrm{tensorPlace}_v\,t$ is integral in the above sense for all $v \notin S$, and $W(t) = 0$ whenever $\mathrm{tensorPlace}_v\,t$ fails to be integral for some $v \notin S$, one has $\int W \, d\tau = c_T \, (\int W_a \, d\tau_a) \prod_{v \in S} \int W_{S,v} \, d\tau_f(v)$. The hypotheses on $\tau$ and $\tau_a$ quantify over all complex-valued functions $g$ with no measurability restriction, the integrals being Bochner integrals in Mathlib's convention.
--
--   This is the restricted-product (Fubini) factorisation of integrals over the $\sigma$-twisted centraliser of a regular diagonal class, in the form needed for twisted orbital integrals in the cyclic base-change step: the point of the statement is that the comparison constant $c_T$ may be chosen once and for all, independently of the class $(t,\delta)$ and of the admissible measures, in contrast with the per-class existence result it cites. It feeds the bound for orbital integrals over double cosets, [`AutomorphicForm.exists_forall_lintegral_orbital_doubleCoset_le_mul_prod_rpow_measure`](thm.html#AutomorphicForm.exists_forall_lintegral_orbital_doubleCoset_le_mul_prod_rpow_measure).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_pos_forall_integral_twistedCentralizer_eq_mul_integral_tensorArch_mul_prod_integral_tensorPlace_of_diagonal.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.exists_pos_forall_integral_twistedCentralizer_eq_mul_integral_tensorArch_mul_prod_integral_tensorPlace_of_diagonal
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ] (νK : Measure (AdeleRing (𝓞 K) K)ˣ)
    [νK.IsHaarMeasure]
    [MeasurableSpace (InfiniteAdeleRing K)ˣ] [BorelSpace (InfiniteAdeleRing K)ˣ] (νA : Measure (InfiniteAdeleRing K)ˣ)
    [νA.IsHaarMeasure]
    (cτ : ℝ) (hcτ : 0 < cτ) :
    ∃ cT : ℝ, 0 < cT ∧
    ∀ (t : GL (Fin 2) L), (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 → (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 →
      Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1 →
    ∀ (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)),
      AutomorphicForm.baseChangeGL K L δ = AutomorphicForm.globalPoints (𝓞 L) L t →
    ∀ (τ : @Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ)
        (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ δ)),
      @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ δ) τ →
      (∀ g : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℂ,
        ∫ s : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ,
            g (s : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) ∂τ =
          cτ * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ,
            g (AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (diagUnits2 p.1 p.2)) ∂(νK.prod νK)) →
    ∀ (τa : @Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ
          (AutomorphicForm.tensorArch K L δ))
        (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ
          (AutomorphicForm.tensorArch K L δ))),
      @Measure.IsHaarMeasure _ _ _
        (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ
          (AutomorphicForm.tensorArch K L δ)) τa →
      (∀ g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℂ,
        ∫ s : AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ (AutomorphicForm.tensorArch K L δ),
            g (s : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) ∂τa =
          ∫ p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ,
            g (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 p.1 p.2)) ∂(νA.prod νA)) →
    ∀ (τf : ∀ v : HeightOneSpectrum (𝓞 K),
        @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
            (AutomorphicForm.tensorPlace K L v δ))
          (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ
            (AutomorphicForm.tensorPlace K L v δ))),
      (∀ v : HeightOneSpectrum (𝓞 K), @Measure.IsHaarMeasure _ _ _
        (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v δ)) (τf v)) →
      (∀ v : HeightOneSpectrum (𝓞 K),
        τf v (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v) = 1) →
    ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (W : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℂ)
        (Wa : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ
          (AutomorphicForm.tensorArch K L δ)] (fun t => Wa t) τa →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v δ)] (fun t => WS v t) (τf v)) →
        (∀ t : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ,
          (∀ v ∉ S, AutomorphicForm.tensorPlace K L v t ∈ AutomorphicForm.semiLocalIntegralSet K L v) →
            W t = Wa (AutomorphicForm.tensorArch K L t) *
              ∏ v ∈ S, WS v (AutomorphicForm.tensorPlace K L v t)) →
        (∀ t : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ,
          (∃ v ∉ S, AutomorphicForm.tensorPlace K L v t ∉ AutomorphicForm.semiLocalIntegralSet K L v) →
            W t = 0) →
          ∫ t, W t ∂τ = cT * (∫ t, Wa t ∂τa) * ∏ v ∈ S, ∫ t, WS v t ∂(τf v) := by sorry
