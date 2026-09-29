-- Prove2me | Theorems.Thm_AutomorphicForm_TwistedBruhat_lintegral_ne_top_and_integral_iwasawa_unitFibre_eq_mul_integral_finsum_tracePushforward_sub
-- name    : AutomorphicForm.TwistedBruhat.lintegral_ne_top_and_integral_iwasawa_unitFibre_eq_mul_integral_finsum_tracePushforward_sub
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/51041d36-e998-557b-8fa2-479c4212a083
-- title:
--   Unfolding the twisted unipotent kernel along the trace fibration
-- statement:
--   Let $K\subseteq L$ be number fields with $L/K$ Galois, and work with the idele group $(\mathbb A_L)^\times$ and the adele rings $\mathbb A_L$, $\mathbb A_K$ carrying their Borel structures.
--
--   The data are: a Haar measure $\nu_{ZL}$ on $(\mathbb A_L)^\times$ and a set $\Omega_L$ which by `hΩL` is a fundamental domain for the action of the principal ideles, the range of $L^\times\to(\mathbb A_L)^\times$, with respect to $\nu_{ZL}$; an element $D$ of [`M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L`](def/M4aHerbrand_IdeleClassVocab.html#L28), i.e. a monoid homomorphism $\mathrm{Gal}(L/K)\to\mathrm{Aut}_{\mathrm{ring}}(\mathbb A_L)$ which is continuous in each component and which on the image of $L$ agrees with the Galois action on $L$ (its value at $\sigma$ is written $\sigma_D$ below, and `unitsAct D σ` denotes the induced automorphism of $(\mathbb A_L)^\times$); an automorphism $\sigma\in\mathrm{Gal}(L/K)$ together with `hgen`, stating that every $\tau\in\mathrm{Gal}(L/K)$ is an integral power of $\sigma$; a homomorphism $\xi_L$ from the full subgroup $\top$ of $(\mathbb A_L)^\times$ to $\mathbb C^\times$ such that the associated complex-valued function $z\mapsto\xi_L(z)$ is continuous (`hξc`) and is trivial on principal ideles (`hξt`); a continuous, compactly supported function $\varphi$ on $\mathrm{GL}_2(\mathbb A_L)$ (`hφc`, `hφs`); a real truncation parameter $R$; a set $X\subseteq\mathbb A_L$ which by `hX` is an additive fundamental domain for `AdeleRing.principalSubgroup (𝓞 L) L` with respect to `adelicAddHaar (𝓞 L) L`; and a set $\Omega_{2K}\subseteq(\mathbb A_L)^\times$ which is measurable (`hΩ₂Km`) and, by `hΩ₂K`, a fundamental domain with respect to [`NumberField.Idele.idelicHaar L`](def/NumberField_IdeleProductMeasure.html#L391) for the range of the composite $K^\times\to(\mathbb A_K)^\times\to(\mathbb A_L)^\times$, the second map being the base-change homomorphism `TransversalMeasure.idelesBaseChange K L` induced by $\mathbb A_K\to\mathbb A_L$.
--
--   Further, $\mu_K$ is an additive Haar measure on $\mathbb A_K$ normalised by $\mu_K(\mathrm{adelicBox}\,K)=1$ (`hμK1`), and $c\in\mathbb R_{\ge0}^\infty$ is nonzero and finite (`hc0`, `hcT`) and is the constant of the trace fibration: by `hc`, for every measurable $G:\mathbb A_L\to\mathbb R_{\ge0}^\infty$,
--   $$\int^- G\,d(\mathrm{adelicAddHaar}\,L)\;=\;c\int^-_{r\in\mathbb A_K}\int^-_{w}G\bigl(\mathrm{traceFibre}\,K\,L\,r\,w\bigr)\,d\Bigl(\textstyle\prod_{i}\mathrm{adelicAddHaar}\,K\Bigr)\,d\mu_K,$$
--   where $w$ runs over $\mathbb A_K^{\,n}$ with $n=\mathrm{finrank}_K\ker(\mathrm{Tr}_{L/K})$ and $\mathrm{traceFibre}\,K\,L\,r\,w=\beta(r)\cdot[L:K]^{-1}+\sum_i\beta(w_i)\cdot e_i$, with $\beta$ the base-change map $\mathbb A_K\to\mathbb A_L$ and $e_i$ the chosen basis of $\ker(\mathrm{Tr}_{L/K})$.
--
--   Write $g=g(x,t,k)=n(x)\,\mathrm{diag}(t,1)\,k$, where $n(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$, $\mathrm{diag}(t,1)$ is `diagOne t`, and $k$ ranges over the subgroup `adelicMaximalCompact L` of $\mathrm{GL}_2(\mathbb A_L)$ (finite part integral, archimedean components row isometries), equipped with `maximalCompactHaar L`. Write $z\cdot I$ for `centralScalar` and $\|t\|_L$ for `TateGlobal.ideleNorm L t`, the value of the Haar modulus character. Put
--   $$A(x,t,k,\zeta)=\sum^{\mathrm{f}}_{\delta\in S}\varphi\bigl(g^{-1}\,\delta\,\sigma_D(\zeta\cdot I\,g)\bigr)-\mathbf 1\bigl[\mathrm{adelicHeight}\,L(\zeta\cdot I\,g)>e^{R}\bigr]\cdot\int \sum^{\mathrm{f}}_{\delta\in S_0}\varphi\bigl(g^{-1}\,\delta\,\sigma_D(n(q)\,\zeta\cdot I\,g)\bigr)\,d\mathbb P(q),$$
--   where $\delta$ is mapped into $\mathrm{GL}_2(\mathbb A_L)$ by `globalPoints`, $S_0=\{\delta\in\mathrm{GL}_2(L):\delta_{10}=0,\ \delta_{00}=\delta_{11}=1\}$, $S$ is the subset of those $\delta\in S_0$ lying in `TwistedBruhat.normUnipotentSet K L σ hgen`, i.e. whose $\sigma$-twisted conjugacy class has twisted norm class (via `normClassMap hgen`) equal to the conjugacy class of some $\gamma\in\mathrm{GL}_2(K)$ of unipotent type, the sums are finitary sums over these sets, $\mathbb P$ is `adelicAddHaar (𝓞 L) L` conditioned on `adelicBox L`, and the second term is the truncation by the set where the adelic height exceeds $e^{R}$ of the constant term [`AutomorphicForm.constantTerm`](def/AutomorphicForm_ConstantTerm.html#L47) along the unipotent direction. Put further
--   $$\Psi_{t,k,\zeta}(w)=\varphi\bigl(k^{-1}\,n(w\,t^{-1})\,\mathrm{diag}(\sigma_D(t)\,t^{-1},1)\,(\sigma_D(\zeta)\cdot I)\,\sigma_D(k)\bigr),$$
--   $$B(t,k,\zeta)=\sum^{\mathrm{f}}_{\eta\in K^\times}\bigl(\mathrm{tracePushforward}\,K\,L\,\Psi_{t,k,\zeta}\bigr)(\eta)-\Bigl[\text{if }e^{R}<\mathrm{adelicHeight}\,L(\mathrm{diag}(t,1))\ \text{then }\int_{\mathbb A_K}\bigl(\mathrm{tracePushforward}\,K\,L\,\Psi_{t,k,\zeta}\bigr)(r)\,d\mu_K\ \text{else }0\Bigr],$$
--   where $\eta$ is mapped into $\mathbb A_K$ by the structure map, $\sigma_D(t)$ and $\sigma_D(\zeta)$ denote `unitsAct D σ` applied to $t$ and $\zeta$, and $\mathrm{tracePushforward}\,K\,L\,F\,(r)=\int_{w}F(\mathrm{traceFibre}\,K\,L\,r\,w)$ against the product of copies of `adelicAddHaar K`.
--
--   The remaining hypothesis `hfin` is an absolute convergence assumption before unfolding: the iterated lower integral over $x\in X$ against `adelicAddHaar (𝓞 L) L`, then $t\in\Omega_{2K}$ against `idelicHaar L`, then $k$ against `maximalCompactHaar L`, of $\bigl(\int^-_\zeta\|\xi_L(\zeta)\|_e\,\|A(x,t,k,\zeta)\|_e\,d\nu_{ZL}\bigr)\cdot\mathrm{ofReal}\,\|t\|_L^{-1}$ is not $\infty$.
--
--   The conclusion is a conjunction of two assertions.
--
--   First, the corresponding unfolded lower integral is finite: the iterated lower integral over $t\in\Omega_{2K}$ against `idelicHaar L`, then $k$ against `maximalCompactHaar L`, then $\zeta$ against $\nu_{ZL}$, of $\|\xi_L(\zeta)\|_e\,\|B(t,k,\zeta)\|_e\cdot\mathrm{ofReal}\,\|t\|_L^{-1}$ (here the norm factor stands inside the $\zeta$-integrand) is not $\infty$.
--
--   Second, the Bochner integrals satisfy
--   $$\int_{x\in X}\int_{t\in\Omega_{2K}}\int_k\Bigl(\int_\zeta\xi_L(\zeta)\,A(x,t,k,\zeta)\,d\nu_{ZL}\Bigr)\,\|t\|_L^{-1}\,d(\mathrm{maximalCompactHaar}\,L)\,d(\mathrm{idelicHaar}\,L)\,d(\mathrm{adelicAddHaar}\,L)$$
--   $$=\;c_{\mathbb R}\cdot\int_{t\in\Omega_{2K}}\int_k\Bigl(\int_\zeta\xi_L(\zeta)\,B(t,k,\zeta)\,d\nu_{ZL}\Bigr)\,\|t\|_L^{-1}\,d(\mathrm{maximalCompactHaar}\,L)\,d(\mathrm{idelicHaar}\,L),$$
--   the scalar being the complex number determined by the real number `c.toReal`, and $\|t\|_L^{-1}$ being read as a complex scalar. Thus the integration over the adelic fundamental domain $X$ is carried out: the $\delta$-sum over the twisted unipotent classes becomes a sum over $\eta\in K^\times$ of trace push-forwards, and the truncated constant term becomes the corresponding integral of the trace push-forward over $\mathbb A_K$, truncated by the condition $e^R<\mathrm{adelicHeight}\,L(\mathrm{diag}(t,1))$.
--
--   This is the unipotent unfolding step in the $\sigma$-twisted (base-change) trace formula for $\mathrm{GL}_2$: in Iwasawa coordinates the adelic variable $x$ of the unipotent direction is integrated out against the trace fibration $\mathbb A_L\to\mathbb A_K$, turning the sum over twisted unipotent classes into a sum over $K^\times$ of trace push-forwards and the truncated constant term into an integral over $\mathbb A_K$, with the accompanying finiteness of the unfolded absolute integral. It feeds the comparison of the twisted cuspidal kernel with its truncation in [`AutomorphicForm.TwistedBruhat.lintegral_ne_top_and_integral_iwasawa_cuspKernel_sub_cuspTruncation_eq_mul_integral_finsum_tracePushforward_sub`](thm.html#AutomorphicForm.TwistedBruhat.lintegral_ne_top_and_integral_iwasawa_cuspKernel_sub_cuspTruncation_eq_mul_integral_finsum_tracePushforward_sub).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_TwistedBruhat_lintegral_ne_top_and_integral_iwasawa_unitFibre_eq_mul_integral_finsum_tracePushforward_sub.lean

import Definitions.Def_AutomorphicForm_TwistedCuspKernel
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_AdelicTracePushforward
import Definitions.Def_AutomorphicForm_TransversalMeasure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open AutomorphicForm AutomorphicForm.AdelicTracePushforward
open scoped TensorProduct Pointwise ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.TwistedBruhat.lintegral_ne_top_and_integral_iwasawa_unitFibre_eq_mul_integral_finsum_tracePushforward_sub
    (K L : Type)
    [Field K]
    [NumberField K]
    [Field L]
    [NumberField L]
    [Algebra K L]
    [IsGalois K L]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ]
    [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure]
    (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (φ : AdelicGL2 (𝓞 L) L → ℂ)
    (hφc : Continuous φ)
    (hφs : HasCompactSupport φ)
    (R : ℝ)
    (X : Set (AdeleRing (𝓞 L) L))
    (Ω₂K : Set (AdeleRing (𝓞 L) L)ˣ)
    (hX : @IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 L) L) _ _ _
      (NumberField.AdelicHaar.adeleBorel (𝓞 L) L) X (adelicAddHaar (𝓞 L) L))
    (hΩ₂Km : @MeasurableSet _ (NumberField.Idele.ideleBorel L) Ω₂K)
    (hΩ₂K : @IsFundamentalDomain
      ((AutomorphicForm.TransversalMeasure.idelesBaseChange K L).comp
        (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K))).range _ _ _
      (NumberField.Idele.ideleBorel L) Ω₂K (NumberField.Idele.idelicHaar L))
    [MeasurableSpace (AdeleRing (𝓞 K) K)]
    [BorelSpace (AdeleRing (𝓞 K) K)]
    (μK : Measure (AdeleRing (𝓞 K) K))
    [μK.IsAddHaarMeasure]
    (hμK1 : μK (NumberField.AdelicBox.adelicBox K) = 1)
    (c : ℝ≥0∞)
    (hc0 : c ≠ 0)
    (hcT : c ≠ ⊤)
    (hc : ∀ G : AdeleRing (𝓞 L) L → ℝ≥0∞, @Measurable _ _ (NumberField.AdelicHaar.adeleBorel (𝓞 L) L) _ G →
      ∫⁻ x, G x ∂(adelicAddHaar (𝓞 L) L) =
        c * ∫⁻ r, ∫⁻ w, G (traceFibre K L r w)
          ∂(@Measure.pi (Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L)))) (fun _ => AdeleRing (𝓞 K) K) _
            (fun _ => NumberField.AdelicHaar.adeleBorel (𝓞 K) K) (fun _ => adelicAddHaar (𝓞 K) K)) ∂μK)
    (hfin : ∫⁻ x in X, ∫⁻ t in Ω₂K, ∫⁻ k,
            (∫⁻ ζ, ‖((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ)‖ₑ *
              ‖(∑ᶠ δ ∈ {δ : GL (Fin 2) L | δ ∈ TwistedBruhat.normUnipotentSet K L σ hgen ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1},
                  φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                    AutomorphicForm.sigmaAdelicAct K L D σ
                      (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))))) -
                Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
                (@AutomorphicForm.constantTerm _
                  (adeleBorel (𝓞 L) L) _ _
                  (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
                  (fun t => AutomorphicForm.unipotentGL2 t)
                  (fun y => ∑ᶠ δ ∈ {δ : GL (Fin 2) L |
                      (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                      (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1},
                    φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                      AutomorphicForm.sigmaAdelicAct K L D σ y)))
                  (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L)))‖ₑ ∂νZL) *
              ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L t)⁻¹
          ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L)
        ∂(adelicAddHaar (𝓞 L) L) ≠ ⊤) :
    (∫⁻ t in Ω₂K, ∫⁻ k, ∫⁻ ζ, ‖((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ)‖ₑ * ‖((∑ᶠ η : Kˣ, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) (algebraMap K (AdeleRing (𝓞 K) K) (η : K))) -
                (if Real.exp R < NumberField.AdelicHeight.adelicHeight L (diagOne t : AdelicGL2 (𝓞 L) L) then
                  ∫ r, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) r ∂μK else 0))‖ₑ *
          ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L t)⁻¹
        ∂νZL ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L) ≠ ⊤) ∧
    (∫ x in X, ∫ t in Ω₂K, ∫ k,
            (∫ ζ, ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) *
              ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | δ ∈ TwistedBruhat.normUnipotentSet K L σ hgen ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1},
                  φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                    AutomorphicForm.sigmaAdelicAct K L D σ
                      (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))))) -
                Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
                (@AutomorphicForm.constantTerm _
                  (adeleBorel (𝓞 L) L) _ _
                  (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
                  (fun t => AutomorphicForm.unipotentGL2 t)
                  (fun y => ∑ᶠ δ ∈ {δ : GL (Fin 2) L |
                      (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                      (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1},
                    φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                      AutomorphicForm.sigmaAdelicAct K L D σ y)))
                  (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L)))) ∂νZL) *
              (((NumberField.TateGlobal.ideleNorm L t)⁻¹ : ℝ) : ℂ)
          ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L)
        ∂(adelicAddHaar (𝓞 L) L) =
      (c.toReal : ℂ) * ∫ t in Ω₂K, ∫ k, (∫ ζ, ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) * ((∑ᶠ η : Kˣ, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) (algebraMap K (AdeleRing (𝓞 K) K) (η : K))) -
                (if Real.exp R < NumberField.AdelicHeight.adelicHeight L (diagOne t : AdelicGL2 (𝓞 L) L) then
                  ∫ r, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) r ∂μK else 0)) ∂νZL) *
          (((NumberField.TateGlobal.ideleNorm L t)⁻¹ : ℝ) : ℂ)
        ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L)) := by sorry
