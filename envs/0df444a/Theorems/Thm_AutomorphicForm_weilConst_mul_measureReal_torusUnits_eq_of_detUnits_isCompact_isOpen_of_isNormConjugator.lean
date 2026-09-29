-- Prove2me | Theorems.Thm_AutomorphicForm_weilConst_mul_measureReal_torusUnits_eq_of_detUnits_isCompact_isOpen_of_isNormConjugator
-- name    : AutomorphicForm.weilConst_mul_measureReal_torusUnits_eq_of_detUnits_isCompact_isOpen_of_isNormConjugator
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/9133339e-4870-5495-9410-a9e6f53a2ced
-- title:
--   Weil constant times torus unit volume, ramified and unramified cases
-- statement:
--   Throughout, $K$ and $L$ are number fields with $L$ an extension of $K$ of degree $2$ (hypothesis `h2`: $\operatorname{finrank}_K L = 2$), $\sigma$ is a $K$-algebra automorphism of $L$ with the property (`hgen`) that every $K$-automorphism of $L$ lies in the subgroup of integer powers of $\sigma$; $v$ is a nonzero prime of $\mathcal{O}_K$, $K_v$ denotes the completion `v.adicCompletion K`, and all matrix groups are $\mathrm{GL}_2$ over $K_v$ or over $L \otimes_K K_v$. The map [`AutomorphicForm.toTensorGL`](def/AutomorphicForm_TwistedOrbital.html#L71) is the homomorphism $\mathrm{GL}_2(K_v) \to \mathrm{GL}_2(L \otimes_K K_v)$ induced by $a \mapsto 1 \otimes a$, [`AutomorphicForm.sigmaGL`](def/AutomorphicForm_TwistedOrbital.html#L202) is the automorphism of $\mathrm{GL}_2(L \otimes_K K_v)$ induced by $\sigma \otimes \mathrm{id}$, and [`AutomorphicForm.normString`](def/AutomorphicForm_TwistedOrbital.html#L205) of an element $\delta$ is the product $\prod_{i<2} \sigma^i(\delta)$ over the range of $\operatorname{finrank}_K L$. For $\delta \in \mathrm{GL}_2(L\otimes_K K_v)$, [`AutomorphicForm.twistedCentralizer`](def/AutomorphicForm_TwistedOrbital.html#L220) is the subgroup $T_\delta = \{t : t\,\delta\,\sigma(t)^{-1} = \delta\}$, carrying the Borel $\sigma$-algebra of its subspace topology; [`AutomorphicForm.IsNormConjugator`](def/AutomorphicForm_TwistedOrbital.html#L214) for $\gamma$, $\delta$, $y$ asserts $\mathrm{toTensorGL}(\gamma) = y^{-1}\,\mathrm{normString}(\delta)\,y$, and [`AutomorphicForm.IsNormOf`](def/AutomorphicForm_TwistedOrbital.html#L217) asserts that such a $y$ exists; [`AutomorphicForm.IsSigmaConjugate`](def/AutomorphicForm_TwistedOrbital.html#L208) for $\delta,\delta'$ asserts the existence of $x$ with $\delta' = x^{-1}\delta\,\sigma(x)$. For $\gamma \in \mathrm{GL}_2(K_v)$, [`AutomorphicForm.localCentralizer`](def/AutomorphicForm_LocalOrbitalBase.html#L193) is the centralizer of $\{\gamma\}$ in $\mathrm{GL}_2(K_v)$, again with its Borel $\sigma$-algebra, and [`AutomorphicForm.IsRegularSemisimple`](def/AutomorphicForm_LocalOrbitalBase.html#L402) asserts that $(\operatorname{tr} \gamma)^2 - 4\det \gamma$ is a unit.
--
--   The data are: a unit $c \in K_v^\times$ and an element $\delta \in \mathrm{GL}_2(L\otimes_K K_v)$ such that (`hδ`) the scalar matrix $c \cdot 1$ is a norm of $\delta$ in the above sense, and (`hδq`) for no unit $z$ of $L \otimes_K K_v$ is $\delta$ $\sigma$-conjugate to the scalar matrix $z \cdot 1$; a Haar measure $\tau'$ on $T_\delta$; an element $u_0 \in T_\delta$ (`hu₀`); an element $\gamma_0 \in \mathrm{GL}_2(K_v)$ which is regular semisimple (`hγ₀`) and elliptic in the sense (`hγ₀e`) that for no $g \in \mathrm{GL}_2(K_v)$ do both off-diagonal entries of $g^{-1}\gamma_0 g$ vanish; and an element $y_1$ with (`hy₁`) $\mathrm{toTensorGL}(\gamma_0) = y_1^{-1}\,\mathrm{normString}(u_0\delta)\,y_1$.
--
--   Write $S = T_\delta \sqcap T_{u_0\delta}$ for the intersection of the two twisted centralizers, with its Borel $\sigma$-algebra. The structural hypotheses are: (`hS`) an element $t$ of $\mathrm{GL}_2(L\otimes_K K_v)$ lies in $S$ if and only if $t = y_1\,\mathrm{toTensorGL}(m)\,y_1^{-1}$ for some $m$ in the centralizer of $\gamma_0$; Haar measures $\tau_S$ on $S$ (`hτS`) and $\tau_T$ on the centralizer of $\gamma_0$ (`hτT`); (`hlink`) the compatibility of these two measures, namely that the pushforward of $\tau_S$ along $s \mapsto y_1^{-1} s y_1$ coincides, as a measure on $\mathrm{GL}_2(L\otimes_K K_v)$ with its Borel structure, with the pushforward of $\tau_T$ along $m \mapsto \mathrm{toTensorGL}(m)$; (`hdetK`) every $t \in T_\delta$ has $\det t = \iota(s)$ for some $s \in K_v^\times$, where $\iota$ is the map on units induced by $a \mapsto 1 \otimes a$; writing $U \subseteq T_\delta$ for the set of those $t$ whose determinant is $\iota(s)$ for some $s \in K_v^\times$ with $v(s) = 1$, the hypotheses that $U$ is open (`hUo`) and compact (`hUc`); (`hϖ`) the existence of $t \in T_\delta$ whose determinant is $\iota(s)$ for some $s \in K_v^\times$ with $v(s) = \mathrm{WithZero.exp}(-1)$; and (`htr`) integrality of traces on the centralizer of $\gamma_0$: for every $m$ there with $v(\det m) = 1$ one has $v(\operatorname{tr} m) \le 1$.
--
--   Under these hypotheses the assertion is: for every real number $\rho$ with the property that every function $w : T_\delta \to \mathbb{R}$ which is nonnegative, measurable, of compact support and satisfies the normalisation $\int_{s \in S} w(s\,t)\,d\tau_S = 1$ for all $t \in T_\delta$ (the element $s$ of $S$ being regarded in $T_\delta$ through the first component of membership in the intersection) obeys $\int_{T_\delta} w \, d\tau' = \rho$, both of the following hold.
--
--   First, if there exists $t$ in the centralizer of $\gamma_0$ with $v(\det t) = \mathrm{ofAdd}(-1)$, then
--   $$\rho \cdot \big((\mathrm{Subtype.val})_*\tau_T\big)\big(\{g : g \text{ centralizes } \gamma_0,\ v(\det g) = 1,\ v(\operatorname{tr} g) \le 1\}\big) = \tau'(U),$$
--   as an identity of real numbers (the `toReal` of the two measure values).
--
--   Second, if no such $t$ exists, then the same product equals $2\,\tau'(U)$, again as real numbers.
--
--   This is the measure-theoretic half of the local computation of the constant comparing a twisted orbital integral on $\mathrm{GL}_2(L \otimes_K K_v)$ with an elliptic orbital integral on $\mathrm{GL}_2(K_v)$: the volume of the unit-determinant part of the twisted centralizer is compared with the volume of the unit-determinant, integral-trace part of the centralizer of $\gamma_0$, the factor being $1$ or $2$ according to whether the centralizer of $\gamma_0$ contains an element of determinant valuation $-1$. It is used by [`AutomorphicForm.weilConst_mul_measureReal_torusUnits_eq_of_isNormConjugator_of_not_isSigmaConjugate_scalar_of_finrank_eq_two`](thm.html#AutomorphicForm.weilConst_mul_measureReal_torusUnits_eq_of_isNormConjugator_of_not_isSigmaConjugate_scalar_of_finrank_eq_two), where the structural hypotheses about determinants, the compact open unit set and a uniformiser are supplied from the local algebra.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_weilConst_mul_measureReal_torusUnits_eq_of_detUnits_isCompact_isOpen_of_isNormConjugator.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain
open scoped TensorProduct
open scoped TensorProduct.RightActions

theorem AutomorphicForm.weilConst_mul_measureReal_torusUnits_eq_of_detUnits_isCompact_isOpen_of_isNormConjugator
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    (c : (v.adicCompletion K)ˣ)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ)
    (hδq : ∀ z : (L ⊗[K] v.adicCompletion K)ˣ,
      ¬ AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z))
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ')
    (u₀ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hu₀ : u₀ ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)
    (γ₀ : GL (Fin 2) (v.adicCompletion K)) (hγ₀ : AutomorphicForm.IsRegularSemisimple γ₀)
    (hγ₀e : ∀ g : GL (Fin 2) (v.adicCompletion K),
      ¬ (((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 ∧
         ((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0))
    (y₁ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hy₁ : AutomorphicForm.IsNormConjugator K L (v.adicCompletion K) σ γ₀ (u₀ * δ) y₁)
    (hS : ∀ t : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
      t ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
          AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ) ↔
        ∃ m ∈ AutomorphicForm.localCentralizer K v γ₀,
          y₁ * AutomorphicForm.toTensorGL K L (v.adicCompletion K) m * y₁⁻¹ = t)
    (τS : @Measure ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
        AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)) (borel _))
    (hτS : @Measure.IsHaarMeasure _ _ _ (borel _) τS)
    (τT : @Measure (AutomorphicForm.localCentralizer K v γ₀) (AutomorphicForm.localCentralizerBorel K v γ₀))
    (hτT : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ₀) τT)
    (hlink : (letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
       letI := AutomorphicForm.localCentralizerBorel K v γ₀
       letI : MeasurableSpace ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
           AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)) := borel _
       Measure.map (fun s : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
             AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)) =>
           y₁⁻¹ * (s : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * y₁) τS =
         Measure.map (fun m : ↥(AutomorphicForm.localCentralizer K v γ₀) =>
           AutomorphicForm.toTensorGL K L (v.adicCompletion K) (m : GL (Fin 2) (v.adicCompletion K))) τT))
    (hdetK : ∀ t ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ,
      ∃ s : (v.adicCompletion K)ˣ, Matrix.GeneralLinearGroup.det t =
        Units.map (Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s)
    (hUo : IsOpen {t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ) | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 ∧
        Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
          Units.map (Algebra.TensorProduct.includeRight :
            v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s})
    (hUc : IsCompact {t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ) | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 ∧
        Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
          Units.map (Algebra.TensorProduct.includeRight :
            v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s})
    (hϖ : ∃ t ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ,
      ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = WithZero.exp (-1) ∧
        Matrix.GeneralLinearGroup.det t =
          Units.map (Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s)
    (htr : ∀ m ∈ AutomorphicForm.localCentralizer K v γ₀, Valued.v ((m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = 1 →
      Valued.v ((m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace) ≤ 1) :
      (letI := AutomorphicForm.localGLBorel K v
       letI := AutomorphicForm.localCentralizerBorel K v γ₀
       letI := AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ
       ∀ ρ : ℝ,
        (∀ w : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ) → ℝ,
          (letI := AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ
           letI : MeasurableSpace ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
               AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)) := borel _
           (∀ t, 0 ≤ w t) ∧ Measurable w ∧ HasCompactSupport w ∧
             ∀ t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ),
               ∫ s : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
                   AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)),
                 w ((⟨(s : GL (Fin 2) (L ⊗[K] v.adicCompletion K)), (Subgroup.mem_inf.mp s.2).1⟩ :
                   ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)) * t) ∂τS = 1) →
          (letI := AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ
           ∫ t, w t ∂τ' = ρ)) →
        ((∃ t : GL (Fin 2) (v.adicCompletion K), t ∈ AutomorphicForm.localCentralizer K v γ₀ ∧
          Valued.v ((t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = Multiplicative.ofAdd (-1 : ℤ)) →
          ρ * ((Measure.map Subtype.val τT) {g : GL (Fin 2) (v.adicCompletion K) | g ∈ AutomorphicForm.localCentralizer K v γ₀ ∧
            Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = 1 ∧
            Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace) ≤ 1}).toReal = (τ' {t | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 ∧
            Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
              Units.map (Algebra.TensorProduct.includeRight :
                v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s}).toReal) ∧
        ((¬ (∃ t : GL (Fin 2) (v.adicCompletion K), t ∈ AutomorphicForm.localCentralizer K v γ₀ ∧
          Valued.v ((t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = Multiplicative.ofAdd (-1 : ℤ))) →
          ρ * ((Measure.map Subtype.val τT) {g : GL (Fin 2) (v.adicCompletion K) | g ∈ AutomorphicForm.localCentralizer K v γ₀ ∧
            Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = 1 ∧
            Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace) ≤ 1}).toReal = 2 * (τ' {t | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 ∧
            Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
              Units.map (Algebra.TensorProduct.includeRight :
                v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s}).toReal)) := by sorry
