-- Prove2me | Theorems.Thm_AutomorphicForm_setIntegral_canonicalTruncationDomain_adelicKernelHyperbolicPart_sub_indicator_constantTerm_eq_mul_sum_mul_integral_add_sum_of_eq_mul_sum_orbital_add_sum_weightedOrbital
-- name    : AutomorphicForm.setIntegral_canonicalTruncationDomain_adelicKernelHyperbolicPart_sub_indicator_constantTerm_eq_mul_sum_mul_integral_add_sum_of_eq_mul_sum_orbital_add_sum_weightedOrbital
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/91237691-ee7f-520d-84ef-9b49168c05c8
-- title:
--   Centre unfolding of the truncated hyperbolic term over K
-- statement:
--   Throughout, $K$ is a number field, $\mathbb{A}_K$ denotes its adele ring `AdeleRing (𝓞 K) K`, and $\mathrm{GL}_2(\mathbb{A}_K)$ denotes `AdelicGL2 (𝓞 K) K`, carrying the Borel $\sigma$-algebra `glBorel` and the Haar measure `adelicGLHaar (Fin 2) (𝓞 K) K`. The group $\mathbb{A}_K^\times$ is equipped with a measurable space that is the Borel structure of its topology, and with a Haar measure $\nu_{Z}$ (`νZK`). Two real parameters $\alpha<\beta$ with $0<\alpha$ are fixed, together with a set $\Phi_K \subseteq \mathrm{GL}_2(\mathbb{A}_K)$, and a set $\Omega_K \subseteq \mathbb{A}_K^\times$ which by `hΩK` is a fundamental domain for the subgroup of principal ideles, i.e. the range of the map $\mathbb{A}_K^\times \to \mathbb{A}_K^\times$ induced by $K \to \mathbb{A}_K$, acting on $(\mathbb{A}_K^\times,\nu_{Z})$.
--
--   The character data consist of a group homomorphism $\xi$ from the full subgroup $\top \le \mathbb{A}_K^\times$ to $\mathbb{C}^\times$ such that $z \mapsto \xi(z)$ is continuous as a $\mathbb{C}$-valued function (`hξc`) and $\xi$ is trivial on the principal ideles (`hξt`); thus $\xi$ is an idele class character.
--
--   The torus data consist of a subgroup $H_K \le \mathrm{GL}_2(\mathbb{A}_K)$ which is closed (`hHKc`) and which, by `hHK`, consists exactly of those $h$ whose matrix entries at positions $(1,0)$ and $(0,1)$ vanish, i.e. the diagonal subgroup; a Haar measure $\mu_{H_K}$ on $H_K$ which is also right invariant; and a constant $c_{H_K}>0$ such that (`hHKμ`) for every $g : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$,
--   $$\int_{H_K} g(h)\,d\mu_{H_K} = c_{H_K}\int_{\mathbb{A}_K^\times \times \mathbb{A}_K^\times} g\bigl(\mathrm{scalar}(z)\cdot \mathrm{diag}(t,1)\bigr)\,d(\nu_{Z}\otimes\nu_{Z})(z,t),$$
--   where $\mathrm{scalar}(z) =$ `centralScalar (𝓞 K) K z` is the central scalar matrix with entry $z$ and $\mathrm{diag}(t,1) =$ `diagUnits2 t 1`. A further constant $c_{\tau K}>0$ is fixed.
--
--   The centraliser data consist of a family $\tau_K$ assigning to each $\gamma \in \mathrm{GL}_2(K)$ a measure on the centraliser of $\gamma_{\mathbb{A}} :=$ `globalPoints (𝓞 K) K γ` (the image of $\gamma$ under the map induced by $K \to \mathbb{A}_K$) inside $\mathrm{GL}_2(\mathbb{A}_K)$, these centralisers carrying the Borel structure `centralizerBorel`; by `hτK` every $\tau_K\gamma$ is a Haar measure.
--
--   The test function is a continuous $f : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ with compact support. A truncation parameter $R \in \mathbb{R}$ is fixed, together with a finite set $\Delta_f \subseteq \mathrm{GL}_2(K)$ and coefficients $a : \mathrm{GL}_2(K) \to \mathbb{C}$. By `hΔf`, each $\gamma \in \Delta_f$ has vanishing $(1,0)$ and $(0,1)$ entries and its diagonal entries satisfy $\gamma_{00}/\gamma_{11} \neq 1$, so $\Delta_f$ is a finite set of regular diagonal elements. By `hτKc`, for each $\gamma \in \Delta_f$ and every $g : \mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$,
--   $$\int_{\mathrm{Cent}(\gamma_{\mathbb{A}})} g(s)\,d\tau_K\gamma = c_{\tau K}\int_{\mathbb{A}_K^\times\times\mathbb{A}_K^\times} g\bigl(\mathrm{diag}(z,t)\bigr)\,d(\nu_{Z}\otimes\nu_{Z})(z,t).$$
--
--   On the orbit space $H_K \backslash \mathrm{GL}_2(\mathbb{A}_K)$, realised as `MulAction.orbitRel.Quotient HK (AdelicGL2 (𝓞 K) K)` with chosen representatives $q_{\mathrm{out}}$, one takes the measure [`HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 K) K) HK μHK`](def/HaarQuotient.html#L28), the pushforward along the quotient map of the adelic Haar measure weighted by the density [`HaarQuotient.density HK μHK`](def/HaarQuotient.html#L25). Two integrability hypotheses are imposed with respect to this measure, for each $\gamma \in \Delta_f$: `hO` for the class function
--   $$q \longmapsto \int_{\mathbb{A}_K^\times} \xi(z)\, f\bigl(q_{\mathrm{out}}^{-1}\,\gamma_{\mathbb{A}}\,(\mathrm{scalar}(z)\, q_{\mathrm{out}})\bigr)\,d\nu_{Z},$$
--   and `hWO` for the same function multiplied by the real weight
--   $$-\log \mathrm{ht}(q_{\mathrm{out}}) - \log \mathrm{ht}(w\, q_{\mathrm{out}}),$$
--   where $\mathrm{ht} =$ [`NumberField.AdelicHeight.adelicHeight K`](def/NumberField_AdelicHeight.html#L158) and $w =$ `adelicWeyl (𝓞 K) K` is the image of the Weyl element $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ in $\mathrm{GL}_2(\mathbb{A}_K)$.
--
--   The hypothesis `hA` is the assumed class-by-class expansion of the truncated hyperbolic term. Its left-hand side is
--   $$\mathcal{H} := \int_{\mathcal{D}} \Bigl(\int_{\Omega_K} \xi(z)\bigl(\mathcal{K}_{\mathrm{hyp}}(x, \mathrm{scalar}(z)x) - \mathbf{1}_{\{\mathrm{ht} > e^{R}\}}(\mathrm{scalar}(z)x)\cdot C_x(\mathrm{scalar}(z)x)\bigr)\,d\nu_{Z}\Bigr) d\,\mathrm{adelicGLHaar},$$
--   in which: $\mathcal{D} =$ `canonicalTruncationDomain K α β` is the third component of the canonical truncation datum attached to $K,\alpha,\beta$; $\mathcal{K}_{\mathrm{hyp}}(x,y) = \sum^{\mathrm{f}}_{\gamma \in \mathrm{hyperbolicCell}\,K} f(x^{-1}\gamma_{\mathbb{A}} y)$ is `adelicKernelHyperbolicPart`, the finite sum over the hyperbolic conjugacy cell of $\mathrm{GL}_2(K)$; the indicator is that of the set `highSet` $= \{g : e^{R} < \mathrm{ht}(g)\}$; and $C_x$ is the constant term `constantTerm`, i.e. for $g \in \mathrm{GL}_2(\mathbb{A}_K)$,
--   $$C_x(g) = \int_{\mathbb{A}_K} \Bigl(\sum^{\mathrm{f}}_{\gamma} f\bigl(x^{-1}\gamma_{\mathbb{A}}\, u(t) g\bigr)\Bigr) d\nu,$$
--   where $u(t) =$ `unipotentGL2 t` $= \begin{pmatrix}1&t\\0&1\end{pmatrix}$, the inner sum runs over those $\gamma \in \mathrm{GL}_2(K)$ with $\gamma_{10}=0$ and $\gamma_{00}/\gamma_{11} \neq 1$, and the measurable space and measure on $\mathbb{A}_K$ are the `nS` and `ν` components of `productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)`, namely the Borel $\sigma$-algebra `adeleBorel` and the additive adelic Haar measure conditioned on the box `adelicBox K`. The right-hand side of `hA` is
--   $$R\sum_{\gamma \in \Delta_f} 2\,a_\gamma \int_{H_K\backslash \mathrm{GL}_2(\mathbb{A}_K)} \Bigl(\int \xi(z) f\bigl(q_{\mathrm{out}}^{-1}\gamma_{\mathbb{A}}(\mathrm{scalar}(z)q_{\mathrm{out}})\bigr)d\nu_{Z}\Bigr) dq \; + \; \sum_{\gamma \in \Delta_f} a_\gamma \int_{H_K\backslash \mathrm{GL}_2(\mathbb{A}_K)} \bigl(-\log \mathrm{ht}(q_{\mathrm{out}}) - \log \mathrm{ht}(w q_{\mathrm{out}})\bigr)\Bigl(\int \xi(z) f\bigl(q_{\mathrm{out}}^{-1}\gamma_{\mathbb{A}}(\mathrm{scalar}(z)q_{\mathrm{out}})\bigr)d\nu_{Z}\Bigr) dq,$$
--   the quotient integrals being taken against [`HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 K) K) HK μHK`](def/HaarQuotient.html#L28).
--
--   Finally, two families of complex-valued functions $I, J : \mathrm{GL}_2(K) \to \mathbb{A}_K^\times \to \mathbb{C}$ are given. By `hI`, for each $\gamma \in \Delta_f$ and each $z$, the value $I(\gamma,z)$ is an orbital integral in the sense of `IsOrbitalIntegralOn`: there is a section weight $w_0 : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{R}$ which is nonnegative, measurable, compactly supported and satisfies $\int_{\mathrm{Cent}(\gamma_{\mathbb{A}})} w_0(t x)\,d\tau_K\gamma = 1$ whenever $f(\mathrm{scalar}(z)\,x^{-1}\gamma_{\mathbb{A}}x) \neq 0$, and
--   $$I(\gamma,z) = \int_{\mathrm{GL}_2(\mathbb{A}_K)} f\bigl(\mathrm{scalar}(z)\,x^{-1}\gamma_{\mathbb{A}}x\bigr)\,w_0(x)\,d\,\mathrm{adelicGLHaar}.$$
--   By `hJ`, for each $\gamma \in \Delta_f$ and each $z$, the value $J(\gamma,z)$ is a weighted orbital integral in the sense of `IsWeightedOrbitalIntegralOn` for the weight $\mathrm{wt}(x) = -\log \mathrm{ht}(x) - \log \mathrm{ht}(w x)$: there is a section weight $s$ with the same four properties and
--   $$J(\gamma,z) = \int_{\mathrm{GL}_2(\mathbb{A}_K)} f\bigl(\mathrm{scalar}(z)\,x^{-1}\gamma_{\mathbb{A}}x\bigr)\,\mathrm{wt}(x)\,s(x)\,d\,\mathrm{adelicGLHaar}.$$
--
--   The conclusion is a conjunction of three statements. First, for every $\gamma \in \Delta_f$ the function $z \mapsto \xi(z) I(\gamma,z)$ is $\nu_{Z}$-integrable. Second, for every $\gamma \in \Delta_f$ the function $z \mapsto \xi(z) J(\gamma,z)$ is $\nu_{Z}$-integrable. Third, the truncated hyperbolic term $\mathcal{H}$ above is equal to
--   $$R\sum_{\gamma \in \Delta_f} 2\,a_\gamma\Bigl(\frac{c_{\tau K}}{c_{H_K}}\int_{\mathbb{A}_K^\times} \xi(z) I(\gamma,z)\,d\nu_{Z}\Bigr) + \sum_{\gamma \in \Delta_f} a_\gamma \Bigl(\frac{c_{\tau K}}{c_{H_K}}\int_{\mathbb{A}_K^\times} \xi(z) J(\gamma,z)\,d\nu_{Z}\Bigr),$$
--   the real ratio $c_{\tau K}/c_{H_K}$ being coerced into $\mathbb{C}$.
--
--   This is the centre-unfolding step for the hyperbolic part of the truncated trace formula on $\mathrm{GL}_2$ over a number field $K$: it converts the class-by-class expansion over $H_K \backslash \mathrm{GL}_2(\mathbb{A}_K)$ into $\xi$-twisted integrals over the idele class group of ordinary and height-weighted orbital integrals of the central translates of $f$, with the comparison constant $c_{\tau K}/c_{H_K}$ coming from the two normalisations of Haar measure on the diagonal torus. It feeds the extraction of the slope and intercept of the hyperbolic term as an affine function of the truncation parameter $R$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_setIntegral_canonicalTruncationDomain_adelicKernelHyperbolicPart_sub_indicator_constantTerm_eq_mul_sum_mul_integral_add_sum_of_eq_mul_sum_orbital_add_sum_weightedOrbital.lean

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
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_TwistedGeometricRemainder
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.setIntegral_canonicalTruncationDomain_adelicKernelHyperbolicPart_sub_indicator_constantTerm_eq_mul_sum_mul_integral_add_sum_of_eq_mul_sum_orbital_add_sum_weightedOrbital
    (K : Type) [Field K] [NumberField K]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦK : Set (AdelicGL2 (𝓞 K) K))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ] (νZK : Measure (AdeleRing (𝓞 K) K)ˣ)
    [νZK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νZK)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξ ⟨z, Subgroup.mem_top z⟩ = 1)

    (HK : Subgroup (AdelicGL2 (𝓞 K) K)) (hHKc : IsClosed (HK : Set (AdelicGL2 (𝓞 K) K)))
    (hHK : ∀ h : AdelicGL2 (𝓞 K) K, h ∈ HK ↔
      ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0 = 0 ∧
       (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1 = 0))
    (μHK : Measure HK) [μHK.IsHaarMeasure] [μHK.IsMulRightInvariant]
    (cHK : ℝ) (hcHK : 0 < cHK)
    (hHKμ : ∀ g : AdelicGL2 (𝓞 K) K → ℂ,
      ∫ h : HK, g (h : AdelicGL2 (𝓞 K) K) ∂μHK =
        cHK * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ,
          g (AutomorphicForm.centralScalar (𝓞 K) K p.1 * diagUnits2 p.2 1) ∂(νZK.prod νZK))
    (cτK : ℝ) (hcτK : 0 < cτK)

    (τK : ∀ γ : GL (Fin 2) K,
      Measure (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ} : Set (AdelicGL2 (𝓞 K) K))))
    (hτK : ∀ γ : GL (Fin 2) K, (τK γ).IsHaarMeasure)

    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (R : ℝ) (Δf : Finset (GL (Fin 2) K)) (a : GL (Fin 2) K → ℂ)
    (hΔf : ∀ γ ∈ Δf, (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 ∧
      (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 1)
    (hτKc : ∀ γ ∈ Δf, ∀ g : AdelicGL2 (𝓞 K) K → ℂ,
      ∫ s : Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ} : Set (AdelicGL2 (𝓞 K) K)),
          g (s : AdelicGL2 (𝓞 K) K) ∂(τK γ) =
        cτK * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ, g (diagUnits2 p.1 p.2) ∂(νZK.prod νZK))
    (hO : ∀ γ ∈ Δf, Integrable (fun q : MulAction.orbitRel.Quotient HK (AdelicGL2 (𝓞 K) K) => (∫ z, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              f (((q.out : AdelicGL2 (𝓞 K) K))⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ *
                (AutomorphicForm.centralScalar (𝓞 K) K z * ((q.out : AdelicGL2 (𝓞 K) K)))) ∂νZK))
            (HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 K) K) HK μHK))
    (hWO : ∀ γ ∈ Δf, Integrable (fun q : MulAction.orbitRel.Quotient HK (AdelicGL2 (𝓞 K) K) =>
            ((-Real.log (NumberField.AdelicHeight.adelicHeight K (q.out : AdelicGL2 (𝓞 K) K))
              - Real.log (NumberField.AdelicHeight.adelicHeight K
                  (AutomorphicForm.adelicWeyl (𝓞 K) K * (q.out : AdelicGL2 (𝓞 K) K))) : ℝ) : ℂ) * (∫ z, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              f (((q.out : AdelicGL2 (𝓞 K) K))⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ *
                (AutomorphicForm.centralScalar (𝓞 K) K z * ((q.out : AdelicGL2 (𝓞 K) K)))) ∂νZK))
            (HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 K) K) HK μHK))
    (hA : (∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
            (∫ z in ΩK, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (AutomorphicForm.adelicKernelHyperbolicPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) -
              Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
              (@AutomorphicForm.constantTerm _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (fun y => ∑ᶠ γ ∈ {γ : GL (Fin 2) K |
                  (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
                    (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 1},
                  f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ * y)))
              (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
            ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) =
        (R : ℂ) * ∑ γ ∈ Δf, 2 * a γ *
            ∫ q : MulAction.orbitRel.Quotient HK (AdelicGL2 (𝓞 K) K), (∫ z, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              f (((q.out : AdelicGL2 (𝓞 K) K))⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ *
                (AutomorphicForm.centralScalar (𝓞 K) K z * ((q.out : AdelicGL2 (𝓞 K) K)))) ∂νZK)
              ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 K) K) HK μHK) +
        ∑ γ ∈ Δf, a γ *
            ∫ q : MulAction.orbitRel.Quotient HK (AdelicGL2 (𝓞 K) K),
              ((-Real.log (NumberField.AdelicHeight.adelicHeight K (q.out : AdelicGL2 (𝓞 K) K))
                - Real.log (NumberField.AdelicHeight.adelicHeight K
                    (AutomorphicForm.adelicWeyl (𝓞 K) K * (q.out : AdelicGL2 (𝓞 K) K))) : ℝ) : ℂ) * (∫ z, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              f (((q.out : AdelicGL2 (𝓞 K) K))⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ *
                (AutomorphicForm.centralScalar (𝓞 K) K z * ((q.out : AdelicGL2 (𝓞 K) K)))) ∂νZK)
              ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 K) K) HK μHK))

    (I J : GL (Fin 2) K → (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hI : ∀ γ ∈ Δf, ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) (adelicGLHaar (Fin 2) (𝓞 K) K)
        (AutomorphicForm.globalPoints (𝓞 K) K γ) (τK γ)
        (fun g : AdelicGL2 (𝓞 K) K => f (AutomorphicForm.centralScalar (𝓞 K) K z * g)) (I γ z))
    (hJ : ∀ γ ∈ Δf, ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      AutomorphicForm.IsWeightedOrbitalIntegralOn (AdeleRing (𝓞 K) K) (adelicGLHaar (Fin 2) (𝓞 K) K)
        (fun x : AdelicGL2 (𝓞 K) K =>
          -Real.log (NumberField.AdelicHeight.adelicHeight K x)
            - Real.log (NumberField.AdelicHeight.adelicHeight K (AutomorphicForm.adelicWeyl (𝓞 K) K * x)))
        (AutomorphicForm.globalPoints (𝓞 K) K γ) (τK γ)
        (fun g : AdelicGL2 (𝓞 K) K => f (AutomorphicForm.centralScalar (𝓞 K) K z * g)) (J γ z)) :
    (∀ γ ∈ Δf, Integrable (fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * I γ z) νZK) ∧
    (∀ γ ∈ Δf, Integrable (fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * J γ z) νZK) ∧
    (∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
            (∫ z in ΩK, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (AutomorphicForm.adelicKernelHyperbolicPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) -
              Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
              (@AutomorphicForm.constantTerm _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (fun y => ∑ᶠ γ ∈ {γ : GL (Fin 2) K |
                  (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
                    (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 1},
                  f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ * y)))
              (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
            ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) =
      (R : ℂ) * ∑ γ ∈ Δf, 2 * a γ *
          (((cτK / cHK : ℝ) : ℂ) * ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * I γ z ∂νZK) +
      ∑ γ ∈ Δf, a γ *
          (((cτK / cHK : ℝ) : ℂ) * ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * J γ z ∂νZK) := by sorry
