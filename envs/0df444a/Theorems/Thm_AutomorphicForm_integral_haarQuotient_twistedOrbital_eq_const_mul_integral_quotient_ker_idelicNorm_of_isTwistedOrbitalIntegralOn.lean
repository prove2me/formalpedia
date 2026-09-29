-- Prove2me | Theorems.Thm_AutomorphicForm_integral_haarQuotient_twistedOrbital_eq_const_mul_integral_quotient_ker_idelicNorm_of_isTwistedOrbitalIntegralOn
-- name    : AutomorphicForm.integral_haarQuotient_twistedOrbital_eq_const_mul_integral_quotient_ker_idelicNorm_of_isTwistedOrbitalIntegralOn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/cce6fb49-ab45-50cb-90bc-5fefd46a797a
-- title:
--   H-quotient versus norm-one twisted orbital integrals for GL₂
-- statement:
--   Throughout, $K$ and $L$ are number fields with $L/K$ finite Galois, $\mathbb{A}_K=\mathrm{AdeleRing}(\mathcal{O}_K,K)$ and $\mathbb{A}_L=\mathrm{AdeleRing}(\mathcal{O}_L,L)$, and $\mathrm{AdelicGL2}(\mathcal{O}_L,L)=\mathrm{GL}_2(\mathbb{A}_L)$. The idele group $\mathbb{A}_L^\times$ carries its Borel measurable structure and a Haar measure $\nu_{ZL}$, and likewise $\mathbb{A}_K^\times$ carries a Haar measure $\nu_K$.
--
--   The Galois data are: a descent datum $D$ of type [`M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L`](def/M4aHerbrand_IdeleClassVocab.html#L28), that is, a monoid homomorphism $\mathrm{Gal}(L/K)\to \mathrm{Aut}_{\mathrm{ring}}(\mathbb{A}_L)$ compatible with $L\to\mathbb{A}_L$ and continuous in each element; an element $\sigma\in\mathrm{Gal}(L/K)$ with `hgen` asserting that every $\tau\in\mathrm{Gal}(L/K)$ lies in the subgroup of integral powers of $\sigma$; and a character $\xi_L$, a monoid homomorphism from the top subgroup of $\mathbb{A}_L^\times$ to $\mathbb{C}^\times$, subject to `hξc` (the function $z\mapsto \xi_L(z)$ is continuous as a $\mathbb{C}$-valued function) and `hξσ` ($\xi_L(D.\mathrm{unitsAct}\,\sigma\,z)=\xi_L(z)$ for all $z$, where $D.\mathrm{unitsAct}\,\sigma$ is the automorphism of $\mathbb{A}_L^\times$ induced by $D.\mathrm{act}\,\sigma$). Here [`AutomorphicForm.sigmaAdelicAct K L D σ`](def/AutomorphicForm_SigmaAdelicAction.html#L14) is the endomorphism of $\mathrm{GL}_2(\mathbb{A}_L)$ obtained by applying $D.\mathrm{act}\,\sigma$ entrywise, [`AutomorphicForm.globalPoints`](def/AutomorphicForm_AdelicLsXi.html#L15) is the entrywise map $\mathrm{GL}_2(L)\to\mathrm{GL}_2(\mathbb{A}_L)$, and [`AutomorphicForm.centralScalar`](def/AutomorphicForm_AdelicLsXi.html#L18) sends an idele to the corresponding scalar matrix.
--
--   The subgroup $H\le \mathrm{GL}_2(\mathbb{A}_L)$ is assumed closed (`hHc`) and is characterised by `hH`: $h\in H$ if and only if the $(1,0)$ and $(0,1)$ entries of $h$ vanish and $(\mathrm{sigmaAdelicAct}\,\sigma)(h)\,h^{-1}$ lies in the centre of $\mathrm{GL}_2(\mathbb{A}_L)$. It carries a measure $\mu_H$ which is Haar and right invariant.
--
--   The base-change side uses the group $\mathrm{GL}_2(L\otimes_K\mathbb{A}_K)$ with its Borel structure [`AutomorphicForm.glBorelOf`](def/AutomorphicForm_TwistedOrbital.html#L57), a measure $\mu$ on it together with the hypothesis $h\mu$ that $\mu$ is Haar, and the isomorphism [`AutomorphicForm.baseChangeGL K L : GL_2(L⊗_K A_K) → GL_2(A_L)`](def/AutomorphicForm_BaseChangePlaces.html#L69) induced entrywise by the ring isomorphism $L\otimes_K\mathbb{A}_K\cong\mathbb{A}_L$. Four positive normalising constants are posited through explicit integration formulas, valid for all $\mathbb{C}$-valued integrands:
--
--   (i) $c_\mu>0$ with `hμc`: $\int F(\mathrm{baseChangeGL}\,x)\,d\mu = c_\mu \int F\,d(\mathrm{adelicGLHaar}(\mathrm{Fin}\,2,\mathcal{O}_L,L))$;
--
--   (ii) $c_H>0$ with the hypothesis again named `hHc` (which shadows the closedness hypothesis of that name): $\int_H g\,d\mu_H = c_H\int_{\mathbb{A}_L^\times\times\mathbb{A}_K^\times} g\big(\mathrm{centralScalar}(p_1)\cdot \mathrm{baseChangeGL}(\mathrm{toTensorGL}(\mathrm{diagUnits2}\,p_2\,1))\big)\,d(\nu_{ZL}\otimes\nu_K)$, where $\mathrm{diagUnits2}\,x\,y$ is the diagonal matrix with entries $x,y$ and `toTensorGL` is induced by $\mathbb{A}_K\to L\otimes_K\mathbb{A}_K$, $a\mapsto 1\otimes a$;
--
--   (iii) $c_\tau>0$, used only in the conclusion;
--
--   (iv) $c_N>0$ with `hNc`: $\int_{N^1} g\,d\mu_N = c_N\int_{q} g\big((D.\mathrm{unitsAct}\,\sigma)(q.\mathrm{out})\cdot (q.\mathrm{out})^{-1}\big)\,d(\mathrm{HaarQuotient.measure}\,\nu_{ZL}\,A_K\,\mu_{A_K})$, the integral being over the orbit quotient of $\mathbb{A}_L^\times$ by $A_K$ and evaluated on chosen representatives $q.\mathrm{out}$.
--
--   Two further subgroups of $\mathbb{A}_L^\times$ occur, each assumed closed: $A_K$, characterised by `hAK` as the image of $\mathbb{A}_K^\times$ under the unit map of the ring homomorphism $\beta$ of [`M4aHerbrand.GenuineDescent.genuineBaseChange K L`](def/M4aHerbrand_GenuineDescent.html#L87), with Haar measure $\mu_{A_K}$ satisfying `hμAK` ($\int_{A_K} g\,d\mu_{A_K}=\int_{\mathbb{A}_K^\times} g(\beta(a))\,d\nu_K$); and $N^1$, characterised by `hN1` as the kernel of the idelic norm of `genuineBaseChange K L` (the unit map of $\mathrm{Algebra.norm}$ for $\mathbb{A}_L$ over $\mathbb{A}_K$), with Haar measure $\mu_N$. In all quotient integrals, [`HaarQuotient.measure μ H μH`](def/HaarQuotient.html#L28) denotes the pushforward along $G\to \mathrm{MulAction.orbitRel.Quotient}\,H\,G$ of $\mu$ weighted by the density [`HaarQuotient.density H μH`](def/HaarQuotient.html#L25).
--
--   Under these hypotheses the assertion is: for every $t\in\mathrm{GL}_2(L)$ whose $(1,0)$ and $(0,1)$ entries vanish and with $N_{L/K}(t_{00}/t_{11})\neq 1$; for every $\delta\in\mathrm{GL}_2(L\otimes_K\mathbb{A}_K)$ with $\mathrm{baseChangeGL}\,\delta = \mathrm{globalPoints}\,t$; for every measure $\tau$ on the twisted centraliser $\mathrm{twistedCentralizer}\,K\,L\,\mathbb{A}_K\,\sigma\,\delta=\{s : s\,\delta\,(\mathrm{sigmaGL}\,s)^{-1}=\delta\}$ (with its Borel structure) which is Haar and satisfies the factorisation $\int_{s} g(s)\,d\tau = c_\tau\int_{\mathbb{A}_K^\times\times\mathbb{A}_K^\times} g(\mathrm{toTensorGL}(\mathrm{diagUnits2}\,p_1\,p_2))\,d(\nu_K\otimes\nu_K)$ for all $g$; and for every continuous, compactly supported $\varphi:\mathrm{GL}_2(\mathbb{A}_L)\to\mathbb{C}$, both of the following hold.
--
--   First conjunct. For every $I:\mathbb{A}_L^\times\to\mathbb{C}$ such that for all $w\in\mathbb{A}_L^\times$ the value $I(w)$ is a twisted orbital integral of $(g\mapsto \varphi(\mathrm{centralScalar}(w)\cdot g))\circ\mathrm{baseChangeGL}$ at $\delta$ with respect to $\mu$ and $\tau$ — in the sense of `IsTwistedOrbitalIntegralOn`, i.e. there is a section function $w'\ge 0$, measurable with compact support, with $\int_{s} w'(s\,x)\,d\tau = 1$ whenever the integrand does not vanish at $x^{-1}\delta\,\mathrm{sigmaGL}(x)$, and $I(w)=\int x\mapsto \varphi(\mathrm{centralScalar}(w)\cdot\mathrm{baseChangeGL}(x^{-1}\delta\,\mathrm{sigmaGL}\,x))\,w'(x)\,d\mu$ — if the function
--   $$q\mapsto \int_{\mathbb{A}_L^\times} \xi_L(z)\,\varphi\big((q.\mathrm{out})^{-1}\,\mathrm{globalPoints}(t)\,(\mathrm{sigmaAdelicAct}\,\sigma)(\mathrm{centralScalar}(z)\cdot q.\mathrm{out})\big)\,d\nu_{ZL}$$
--   on the orbit quotient of $\mathrm{GL}_2(\mathbb{A}_L)$ by $H$ is integrable for $\mathrm{HaarQuotient.measure}(\mathrm{adelicGLHaar})\,H\,\mu_H$, then (a) the function $wq\mapsto \xi_L(wq.\mathrm{out})\,I(wq.\mathrm{out})$ on the orbit quotient of $\mathbb{A}_L^\times$ by $N^1$ is integrable for $\mathrm{HaarQuotient.measure}\,\nu_{ZL}\,N^1\,\mu_N$, and (b) the integral of the displayed function over the $H$-quotient equals $\big(c_N c_\tau/(c_H c_\mu)\big)$, coerced to $\mathbb{C}$, times $\int \xi_L(wq.\mathrm{out})\,I(wq.\mathrm{out})$ over the $N^1$-quotient.
--
--   Second conjunct. The same statement with the weight $\mathrm{wt}(x) = -\log \mathrm{adelicHeight}_L(\mathrm{baseChangeGL}\,x) - \log \mathrm{adelicHeight}_L(\mathrm{adelicWeyl}\cdot\mathrm{baseChangeGL}\,x)$, where $\mathrm{adelicWeyl}$ is the global point attached to the antidiagonal matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ and $\mathrm{adelicHeight}_L$ is the product of the archimedean and finite adelic heights: for every $J:\mathbb{A}_L^\times\to\mathbb{C}$ such that for all $w$ the value $J(w)$ is a twisted weighted orbital integral (`IsTwistedWeightedOrbitalIntegralOn`, the same section-function condition with the extra factor $\mathrm{wt}(x)$ in the integrand) of $(g\mapsto\varphi(\mathrm{centralScalar}(w)\cdot g))\circ\mathrm{baseChangeGL}$ at $\delta$ with respect to $\mu$ and $\tau$, if the function on the $H$-quotient given by the product of $\big(-\log \mathrm{adelicHeight}_L(q.\mathrm{out})-\log \mathrm{adelicHeight}_L(\mathrm{adelicWeyl}\cdot q.\mathrm{out})\big)$ with the above inner $\nu_{ZL}$-integral is integrable for $\mathrm{HaarQuotient.measure}(\mathrm{adelicGLHaar})\,H\,\mu_H$, then $wq\mapsto \xi_L(wq.\mathrm{out})\,J(wq.\mathrm{out})$ is integrable on the $N^1$-quotient and the integral of that weighted function over the $H$-quotient equals $\big(c_N c_\tau/(c_H c_\mu)\big)$ times $\int \xi_L(wq.\mathrm{out})\,J(wq.\mathrm{out})$ over the $N^1$-quotient.
--
--   This is the change-of-currency identity for the hyperbolic contributions in the $\sigma$-twisted trace formula for $\mathrm{GL}_2$ over a cyclic extension $L/K$: the same term is written once as an integral over $H\backslash\mathrm{GL}_2(\mathbb{A}_L)$ with the $\xi_L$-integral over the centre inside, and once as an integral over $\mathbb{A}_L^\times/N^1$ of twisted (respectively twisted weighted) orbital integrals computed with section functions on the twisted centraliser, the two being proportional with the explicit constant $c_Nc_\tau/(c_Hc_\mu)$. It is used in the evaluation of truncated hyperbolic terms and in the bounds for orbital integrals over double cosets.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integral_haarQuotient_twistedOrbital_eq_const_mul_integral_quotient_ker_idelicNorm_of_isTwistedOrbitalIntegralOn.lean

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

theorem AutomorphicForm.integral_haarQuotient_twistedOrbital_eq_const_mul_integral_quotient_ker_idelicNorm_of_isTwistedOrbitalIntegralOn
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξσ : ∀ z : (AdeleRing (𝓞 L) L)ˣ, ξL ⟨D.unitsAct σ z, Subgroup.mem_top _⟩ = ξL ⟨z, Subgroup.mem_top z⟩)

    (H : Subgroup (AdelicGL2 (𝓞 L) L)) (hHc : IsClosed (H : Set (AdelicGL2 (𝓞 L) L)))
    (hH : ∀ h : AdelicGL2 (𝓞 L) L, h ∈ H ↔
      ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0 ∧
       (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0 ∧
       AutomorphicForm.sigmaAdelicAct K L D σ h * h⁻¹ ∈ Subgroup.center (AdelicGL2 (𝓞 L) L)))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]

    (μ : @Measure (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)))
    (hμ : @Measure.IsHaarMeasure (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) _ _
      (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)) μ)

    (cμ : ℝ) (hcμ : 0 < cμ)
    (hμc : ∀ F : AdelicGL2 (𝓞 L) L → ℂ,
      ∫ x, F (AutomorphicForm.baseChangeGL K L x) ∂μ = cμ * ∫ g, F g ∂(adelicGLHaar (Fin 2) (𝓞 L) L))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ] (νK : Measure (AdeleRing (𝓞 K) K)ˣ)
    [νK.IsHaarMeasure]
    (cH : ℝ) (hcH : 0 < cH)
    (hHc : ∀ g : AdelicGL2 (𝓞 L) L → ℂ,
      ∫ h : H, g (h : AdelicGL2 (𝓞 L) L) ∂μH =
        cH * ∫ p : (AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K)ˣ,
          g (AutomorphicForm.centralScalar (𝓞 L) L p.1 *
            AutomorphicForm.baseChangeGL K L
              (AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (diagUnits2 p.2 1))) ∂(νZL.prod νK))
    (cτ : ℝ) (hcτ : 0 < cτ)
    (AK : Subgroup (AdeleRing (𝓞 L) L)ˣ) (hAKc : IsClosed (AK : Set (AdeleRing (𝓞 L) L)ˣ))
    (hAK : ∀ z : (AdeleRing (𝓞 L) L)ˣ, z ∈ AK ↔ ∃ a : (AdeleRing (𝓞 K) K)ˣ,
      z = Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom a)
    (μAK : Measure AK) [μAK.IsHaarMeasure]
    (hμAK : ∀ g : (AdeleRing (𝓞 L) L)ˣ → ℂ,
      ∫ a : AK, g (a : (AdeleRing (𝓞 L) L)ˣ) ∂μAK =
        ∫ a, g (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom a) ∂νK)
    (N1 : Subgroup (AdeleRing (𝓞 L) L)ˣ) (hN1c : IsClosed (N1 : Set (AdeleRing (𝓞 L) L)ˣ))
    (hN1 : ∀ z : (AdeleRing (𝓞 L) L)ˣ, z ∈ N1 ↔
      (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z = 1)
    (μN : Measure N1) [μN.IsHaarMeasure]
    (cN : ℝ) (hcN : 0 < cN)
    (hNc : ∀ g : (AdeleRing (𝓞 L) L)ˣ → ℂ,
      ∫ n : N1, g (n : (AdeleRing (𝓞 L) L)ˣ) ∂μN =
        cN * ∫ q : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ,
          g (D.unitsAct σ q.out * (q.out)⁻¹) ∂(HaarQuotient.measure νZL AK μAK)) :
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
    ∀ (φ : AdelicGL2 (𝓞 L) L → ℂ), Continuous φ → HasCompactSupport φ →

    (∀ (I : (AdeleRing (𝓞 L) L)ˣ → ℂ),
      (∀ w : (AdeleRing (𝓞 L) L)ˣ,
        AutomorphicForm.IsTwistedOrbitalIntegralOn K L (AdeleRing (𝓞 K) K) σ μ δ τ
          ((fun g : AdelicGL2 (𝓞 L) L => φ (AutomorphicForm.centralScalar (𝓞 L) L w * g)) ∘
            AutomorphicForm.baseChangeGL K L) (I w)) →
      Integrable (fun q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L) =>
            (∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L)))) ∂νZL))
        (HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH) →
      Integrable (fun wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ =>
          ((ξL ⟨(wq.out : (AdeleRing (𝓞 L) L)ˣ), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) * I wq.out)
        (HaarQuotient.measure νZL N1 μN) ∧
      ∫ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L),
            (∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L)))) ∂νZL)
          ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH) =
        ((cN * cτ / (cH * cμ) : ℝ) : ℂ) * ∫ wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ,
          ((ξL ⟨(wq.out : (AdeleRing (𝓞 L) L)ˣ), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) * I wq.out
          ∂(HaarQuotient.measure νZL N1 μN)) ∧

    (∀ (J : (AdeleRing (𝓞 L) L)ˣ → ℂ),
      (∀ w : (AdeleRing (𝓞 L) L)ˣ,
        AutomorphicForm.IsTwistedWeightedOrbitalIntegralOn K L (AdeleRing (𝓞 K) K) σ μ
          (fun x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) =>
            -Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.baseChangeGL K L x))
              - Real.log (NumberField.AdelicHeight.adelicHeight L
                  (AutomorphicForm.adelicWeyl (𝓞 L) L * AutomorphicForm.baseChangeGL K L x)))
          δ τ
          ((fun g : AdelicGL2 (𝓞 L) L => φ (AutomorphicForm.centralScalar (𝓞 L) L w * g)) ∘
            AutomorphicForm.baseChangeGL K L) (J w)) →
      Integrable (fun q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L) =>
            ((-Real.log (NumberField.AdelicHeight.adelicHeight L (q.out : AdelicGL2 (𝓞 L) L))
                - Real.log (NumberField.AdelicHeight.adelicHeight L
                    (AutomorphicForm.adelicWeyl (𝓞 L) L * (q.out : AdelicGL2 (𝓞 L) L))) : ℝ) : ℂ) * (∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L)))) ∂νZL))
        (HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH) →
      Integrable (fun wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ =>
          ((ξL ⟨(wq.out : (AdeleRing (𝓞 L) L)ˣ), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) * J wq.out)
        (HaarQuotient.measure νZL N1 μN) ∧
      ∫ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L),
            ((-Real.log (NumberField.AdelicHeight.adelicHeight L (q.out : AdelicGL2 (𝓞 L) L))
                - Real.log (NumberField.AdelicHeight.adelicHeight L
                    (AutomorphicForm.adelicWeyl (𝓞 L) L * (q.out : AdelicGL2 (𝓞 L) L))) : ℝ) : ℂ) * (∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L)))) ∂νZL)
          ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH) =
        ((cN * cτ / (cH * cμ) : ℝ) : ℂ) * ∫ wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ,
          ((ξL ⟨(wq.out : (AdeleRing (𝓞 L) L)ˣ), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) * J wq.out
          ∂(HaarQuotient.measure νZL N1 μN)) := by sorry
